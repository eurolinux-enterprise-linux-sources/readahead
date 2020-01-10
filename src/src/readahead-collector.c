
/*
 * RAC - ReadAhead Collector daemon
 *
 * Copyright (C) 2006,2007  Red Hat, Inc.
 * Karel Zak <kzak@redhat.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software Foundation,
 * Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

#define _GNU_SOURCE	/* strndup() */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>
#include <signal.h>
#include <fcntl.h>
#include <libaudit.h>
#include <auparse.h>
#include <ctype.h>
#include <sys/param.h>
#include <limits.h>
#include <syslog.h>


/*
 * Defauls
 */
#define CFG_DEFAULT_PATH	"/etc/readahead.conf"
#define CFG_DEFAULT_INIT	"/sbin/init"
#define CFG_DEFAULT_RAWLOG	NULL
#define CFG_DEFAULT_LISTSPATH	NULL
#define CFG_DEFAULT_LISTSEP	"/etc/init.d/readahead_later"

#define MAX_READLINKS 32

#ifndef HAVE_AUDITD_REPLY_LIST
struct auditd_reply_list {
        struct audit_reply reply;
        struct auditd_reply_list *next;
        int ack_socket;
        unsigned long sequence_id;
};
#endif

/* daemon initialization pipe */
static int init_pipe[2];

/* use RacStatus -- this one is for atexit() only */
static int audit_fd = -1;

/*  argv[0] */
static char *progname;

/* reports error and call exit */
FILE *error_out;
#define die(_fmt, ...)	\
		do { \
			if (error_out) { \
				fprintf(error_out, "%s: ERROR: ", progname); \
				fprintf(error_out, _fmt, ## __VA_ARGS__); \
				fputc('\n', error_out); \
				exit(EXIT_FAILURE); \
			} \
                        syslog(LOG_DAEMON|LOG_ERR, _fmt, ## __VA_ARGS__); \
		} while(0)

/* debug output */
int has_debug = 0;
FILE *debug_out;

#define debug(_fmt, ...) \
		do { \
			if (has_debug && debug_out) { \
				fputs("***DEBUG: ", debug_out); \
				fprintf(debug_out, _fmt, ## __VA_ARGS__); \
				fputc('\n', debug_out); \
			} \
		} while(0)

/* daemon specific audit rule */
static struct audit_rule_data *audit_rule;

/* Filter for audit events */
#define IS_EVENT_WANTED(_r) \
		(((_r)->type == AUDIT_PATH || \
		  (_r)->type == AUDIT_CWD  || \
		  (_r)->type == AUDIT_SYSCALL) && \
 		 (_r)->len)

/* Changes by signal handler */
static int has_signal;

/* Statuses */
#define CHILD_SUCCESS 0
#define CHILD_FAILURE 1

/*
 * The readahead-collector has to store all audit events in memory. We cannot
 * write these data to file, because we have to be able to run on system with
 * read-only root FS (early time during boot process).
 *
 * To avoid huge number of allocations we allocate large block(s) and store
 * every new event string to the block. If the actual block is full we allocate
 * a new one and add than to list of block.
 */

#define MEMBLK_SIZE (1024*1024)

typedef struct RacBlock
{
	char buff[ MEMBLK_SIZE ];
	char *pos;
	struct RacBlock *next;
} RacBlock;

/*
 * Daemon modes
 */
typedef enum
{
	RAC_MODE_BG = 0,
	RAC_MODE_INIT = 1,	/* PID=1 */
	RAC_MODE_FG = 2
} RacMode;

/*
 * Daemon status & config struct
 */
typedef struct
{
	RacMode		mode;
	int		maxtime;
	char		*cfg_path;
	char		*rawlog;
	char		*listspath;
	char		*initpath;
	char		*listbgn;
	char		*listsep;
	char		**execign;
	char		*debuglog;
	char		**excludes;
	char		**argv;
	int		argc;
	int		fd;		/* audit fd */
	int		nevents;	/* number of audit events */
	int		nrecords;	/* number of audit records */
	RacBlock	*b_first;
	RacBlock	*b_last;
} RacStatus;

#define is_foreground(_s)	((_s)->mode == RAC_MODE_FG)
#define is_background(_s)	((_s)->mode == RAC_MODE_BG || (_s)->mode == RAC_MODE_INIT)
#define is_init(_s)		((_s)->mode == RAC_MODE_INIT)


static int cfg_read(RacStatus *rac);
static char *cfg_get_item(char *str, const char *name);
static void exec_init(RacStatus *rad);
static int daemon_create(RacStatus *rac);
static void daemon_child_status(int status);
static void clean_audit(void);
static void sig_handler( int sig );
static int insert_rule(RacStatus *rac);
static void delete_rule();
static RacBlock *block_new(RacStatus *rac);
static int block_add_event(RacStatus *rac, const struct audit_reply *rep);
static int blocks_dump(RacStatus *rac, char *filename);
static void blocks_free(RacStatus *rac);
static char **blocks_to_array(RacStatus *rac);
static char *myrealpath(const char *path, char *resolved_path,
				int maxreslth, const char *cwd);
static char **parse_events(RacStatus *rac, char **ary, int *early, int *later);
static int list_write(RacStatus *rac, char **list, int size,
				const char *filetpl, const char *fileext);
static int blocks_dump_as_lists(RacStatus *rac, const char *filename_tpl);
static char *btrim(char *str);
static char **string_to_array(char *data);
static int exclude_file(char **list, const char *filename);

int
main(int argc, char **argv)
{
	RacStatus _rac, *rac = &_rac;
	struct auditd_reply_list *rep = NULL;
	fd_set read_mask;
	struct sigaction sa;
	int i;
	char *p;

	debug_out = stderr;
	error_out = stderr;

	progname = argv[0];
	if ((p = strrchr(argv[0], '/')))
		progname = p+1;

	if (getuid() != 0)
		die("you must be root to run this program.");

        openlog("readahead-collector", LOG_CONS, LOG_DAEMON);

	memset(rac, 0, sizeof(*rac));

	rac->mode = getpid() == 1 ? RAC_MODE_INIT : RAC_MODE_BG;
	rac->cfg_path = CFG_DEFAULT_PATH;
	rac->initpath = CFG_DEFAULT_INIT;
	rac->rawlog = CFG_DEFAULT_RAWLOG;
	rac->listspath = CFG_DEFAULT_LISTSPATH;
	rac->listsep = CFG_DEFAULT_LISTSEP;
	rac->argv = argv;
	rac->argc = argc;

	if (is_init(rac))
		fprintf(error_out, "\n\n***** Readahead Collector Started *****\n\n");

	sa.sa_flags = 0 ;
	sigemptyset( &sa.sa_mask ) ;
	sa.sa_handler = SIG_IGN;
	for (i=1; i < NSIG; i++)
		sigaction( i, &sa, NULL );
	sa.sa_handler = sig_handler;
	sigaction( SIGTERM, &sa, NULL );
	sa.sa_handler = sig_handler;
	sigaction( SIGQUIT, &sa, NULL );
	sa.sa_handler = sig_handler;
	sigaction( SIGINT, &sa, NULL );
	sa.sa_handler = sig_handler;
	sigaction( SIGALRM, &sa, NULL );

	if (argc > 1 && getpid() > 1) {
		for (i=1; i<argc; i++) {

			if (strcmp(argv[i], "-f") == 0)
				rac->mode = RAC_MODE_FG;

			if (strcmp(argv[i], "-d") == 0)
				has_debug = 1;

			else if (strcmp(argv[i], "-h") == 0) {
				fprintf(stdout, "\n%s: [-fh]\n"
					"   -d  enable debug mode \n"
					"   -f  leave the daemon in the foreground for debugging, "
					        "output goes to stdout\n"
					"   -h  this help\n\n", progname);
				exit(EXIT_SUCCESS);
			}
		}
	}

	debug("debug mode ON");

	if (is_init(rac))
		debug("init mode");

	/* Read config file */
	if (cfg_read(rac) != 0) {
		if (is_init(rac))
			exec_init(rac);
		die("cannot read config file");
	}

	/* Transform this process to daemon */
	if (is_background(rac) && daemon_create(rac) < 0) {
		daemon_child_status(CHILD_FAILURE);
		die("cannot daemonize: %s", strerror(errno));
	}

	/* At exit cleanups */
	atexit(clean_audit);

	/* Open way to audit */
	if ((audit_fd = audit_open()) < 0) {
		daemon_child_status(CHILD_FAILURE);
		die("cannot open netlink audit socket");
	}
	rac->fd = audit_fd;

	/* Tell the kernel we are alive */
	if (audit_set_pid(rac->fd, getpid(), WAIT_YES) < 0) {
		daemon_child_status(CHILD_FAILURE);
		die("cannot set PID");
	}

	/* Tell parent that everything os OK */
	if (!is_foreground(rac)) {
		daemon_child_status(CHILD_SUCCESS);
		error_out = debug_out = NULL;
	}

	/* Enable audit */
	if (audit_set_enabled(rac->fd, 1) < 0)
		die("cannot enable audit");

	/* Set size of audit log in kernel */
	if (audit_set_backlog_limit(rac->fd, 256) > 0)
		audit_request_status(rac->fd);
	else
		die("cannot enlarge log limit");

	/* Don't disturb user with my problems... */
	if (audit_set_failure(rac->fd, 0) > 0)
		audit_request_status(rac->fd);
	else
		die("cannot set silent mode");

	/* Add new rules to audit system */
	if (insert_rule(rac) != 0)
		die("cannot insert audit rules");

	/* We don't  want to run forever... */
	alarm(rac->maxtime);

	/* reply */
	if (!(rep = malloc(sizeof(*rep))))
		die("cannot allocate new reply struct");

	/* Main loop */
	for (;;) {
		struct timeval tv;
		int    retval;

		do {
			tv.tv_sec = 30;
			tv.tv_usec = 0;
			FD_ZERO(&read_mask);
			FD_SET(rac->fd, &read_mask);

			retval = select(rac->fd+1, &read_mask, NULL, NULL, &tv);

		} while (retval == -1 && errno == EINTR && has_signal == 0);

		if (has_signal) {
		       delete_rule();
	               audit_set_enabled(audit_fd, 0);
		}

		retval = audit_get_reply(rac->fd, &rep->reply,
				GET_REPLY_NONBLOCKING, 0);

		if (retval > 0 && IS_EVENT_WANTED(&rep->reply))
			block_add_event(rac, &rep->reply);

		if (has_debug && is_background(rac) &&
				debug_out == NULL && rac->debuglog) {
			/*  the root might be already read-write */
			error_out = debug_out = fopen(rac->debuglog, "w");
		}

		if (has_signal)
			break;
	}

	debug("starting reordering data");

	/* disable audit */
	clean_audit();
	rac->fd = -1;

	/* write raw data to file */
	if (rac->rawlog)
		blocks_dump(rac, rac->rawlog);

	/* parse & write data to lists of files */
	if (rac->listspath)
		blocks_dump_as_lists(rac, rac->listspath);

	/* clean up  */
	blocks_free(rac);

	debug("done: success");

	if (has_debug && is_background(rac) && debug_out != stderr)
		fclose(debug_out);

	exit(EXIT_SUCCESS);
}

/*
 * Reads config file
 *
 * - missing or empty file is not error (in particular case
 *   prog. uses default values).
 */
static int
cfg_read(RacStatus *rac)
{
	char buff[BUFSIZ];
	FILE *f;
	struct stat st;

	if (stat(rac->cfg_path, &st) != 0)
		return 0;
	if (st.st_size == 0)
		return 0;
	if (!(f = fopen(rac->cfg_path, "r"))) {
		perror(rac->cfg_path);
		return -1;
	}

	debug("reading config file: %s", rac->cfg_path);

	while(fgets(buff, sizeof(buff), f)) {
		char *p;

		if ((p = strchr(buff, '#')))
			*p = '\0';
		if (!*buff)
			continue;
		if ((p = cfg_get_item(buff, "RAC_RAWLOG")))
			rac->rawlog = strdup(p);
		else if ((p = cfg_get_item(buff,  "RAC_MAXTIME")))
			 rac->maxtime = strtol(p, NULL, 10);
		else if ((p = cfg_get_item(buff, "RAC_INITPATH")))
			rac->initpath = strdup(p);
		else if ((p = cfg_get_item(buff, "RAC_LISTSPATH")))
			rac->listspath = strdup(p);
		else if ((p = cfg_get_item(buff, "RAC_EXECIGN")))
			rac->execign = string_to_array(p);
		else if ((p = cfg_get_item(buff, "RAC_LISTBEGIN")))
			rac->listbgn = strdup(p);
		else if ((p = cfg_get_item(buff, "RAC_LISTSEP")))
			rac->listsep = strdup(p);
		else if ((p = cfg_get_item(buff, "RAC_EXCLUDE")))
			rac->excludes = string_to_array(p);
		else if ((p = cfg_get_item(buff, "RAC_DEBUG")) &&
				strcasecmp(p, "on") == 0)
			has_debug = 1;
		else if ((p = cfg_get_item(buff, "RAC_DEBUGLOG")))
			rac->debuglog = strdup(p);
	}

	fclose(f);
	return 0;
}

/*
 * Returns pointer to data from name="data"
 */
static char *
cfg_get_item(char *buff, const char *name)
{
	char *p, *data;
	int namelen = strlen(name);

	if ((p = strchr(buff, '=')) == NULL || (p - buff) < namelen)
		return NULL;
	if (*(p+1) != '"')
		return NULL;
	if (strncmp(p - namelen, name, namelen))
		return NULL;
	data = p+2;				/* 2 is =" */

	if ((p = strchr(data, '"')) == NULL)
		return NULL;
	*p = '\0';
	data = btrim(data);
	if (data && *data == '\0')
		data = NULL;

	debug("CFG: %s:\t%s", name, data);

	return data;
}

/*
 * Creates new allocated array from string where
 * items are separated by a space ('aaa bbb ccc')
 */
static char **
string_to_array(char *data)
{
	char *p = data, *l = NULL;
	int items = 1;
	char **res = NULL;
	int i;

	while(*p) {
	       if (isspace((unsigned char) *p) && l &&
			      isspace((unsigned char) *l) == 0)
			items++;
		l = p++;
	}
	if (isspace((unsigned char) *l))
		items--;
	if (items)
		res = (char **) malloc(sizeof(char *) * items + 1);
	if (!res)
		return NULL;
	p = data;

	for (i = 0; i < items && *p; i++) {
		while(*p && isspace((unsigned char) *p))
			p++;
		l = p;
		while(*p && isspace((unsigned char) *p) == 0)
			p++;
		if (*p) {
			*p = '\0';
			p++;
		}
		res[i] = strdup(l);
	}
	res[i] = NULL;

	return res;
}

/*
 * Removes space from begin and end of string
 */
static char *
btrim(char *str)
{
	int	es = 1, bs = 1, size;
	char	*b, *e;

	if (!str)
		return NULL;
	size = strlen(str);

	for(b=str, e=(str+size-1); b < e; ) {
		if (es) {
			if (isspace(*e))
				e--;
			else
				es = 0;
		}
		if (bs)	{
			if (isspace(*b))
				b++;
			else
				bs = 0;
		}
		if (es == 0 && bs == 0)
			break;
	}
	*(e+1) = '\0';

	return b;
}

/*
 * Execute /sbin/init
 */
static void
exec_init(RacStatus *rac)
{
	char **xargv;
	int i;

	if (getpid() != 1)
		abort();	/* paranoid */

	xargv = malloc(rac->argc+1);
	xargv[0] = rac->initpath;

	for (i=1; i < rac->argc; i++)
		xargv[i] = rac->argv[i];

	xargv[rac->argc] =  NULL;

	execv(rac->initpath, xargv);

	die("%s: %s", rac->initpath, strerror(errno));
}

/*
 * This function will take care of becoming a daemon. The parent
 * will wait until the child notifies it by writing into a special
 * pipe to signify that it successfully initialized. This prevents
 * a race in the init script where rules get loaded before the daemon
 * is ready and they wind up in syslog. The child returns 0 on success
 * and nonzero on failure. The parent returns nonzero on failure. On
 * success, the parent calls _exit with 0.
 *
 * (code from the auditd daemon)
 */
static int
daemon_create(RacStatus *rac)
{
	int fd, rc;
	pid_t pid;
	int status;

	if (pipe(init_pipe) || fcntl(init_pipe[0], F_SETFD, FD_CLOEXEC) ||
				fcntl(init_pipe[0], F_SETFD, FD_CLOEXEC))
		return -1;

	pid = fork();
	switch (pid)
	{
		case 0:
			/* No longer need this...   */
			close(init_pipe[0]);

			/* Open stdin,out,err to /dev/null */
			fd = open("/dev/null", O_RDWR);
			if (fd < 0)
				return -1;
			if (dup2(fd, 0) < 0)
				return -1;
			if (dup2(fd, 1) < 0)
				return -1;
			if (dup2(fd, 2) < 0)
				return -1;
			close(fd);

			/* Change to '/' */
			if (chdir("/") != 0)
				return -1;

			/* Change session */
			if (setsid() < 0)
				return -1;
			break;
		case -1:
			return -1;
			break;
		default:
			/* Wait for the child to say its done */
			rc = read(init_pipe[0], &status, sizeof(status));
			if (rc < 0)
				return -1;

			if (is_init(rac))
				exec_init(rac);

			/* Success - die a happy death */
			if (status == CHILD_SUCCESS)
				_exit(EXIT_SUCCESS);
			else
				return -1;
			break;
	}
	return 0;
}

/*
 * Send child status to parent process
 */
static void
daemon_child_status(int status)
{
	int rc;

	do {
		rc = write(init_pipe[1], &status, sizeof(status));
	} while (rc < 0 && errno == EINTR);
}

/*
 * At Exit cleanup
 */
static void
clean_audit(void)
{
	if (audit_fd < 0)
		return;

	delete_rule();
	audit_set_enabled(audit_fd, 0);
	audit_set_pid(audit_fd, 0, WAIT_NO);
	audit_close(audit_fd);

	audit_fd = -1;
}

static void
sig_handler( int sig )
{
	debug("\n\nHAVE SIGNAL %d\n", sig);
	has_signal = 1;
}


/*
 * Inserts new rules to audit system
 */
static int
insert_rule(RacStatus *rac)
{
	int rc = 0;
	int flags = AUDIT_FILTER_EXIT;
	int action = AUDIT_ALWAYS;

	if (audit_rule)
		return -1;

	debug("inserting audit rule");

	audit_rule = malloc(sizeof(struct audit_rule_data));

	if (audit_rule == NULL)
		goto err;

	memset(audit_rule, 0, sizeof(struct audit_rule_data));

	rc |= audit_rule_syscallbyname_data(audit_rule, "open");
	rc |= audit_rule_syscallbyname_data(audit_rule, "openat");
	rc |= audit_rule_syscallbyname_data(audit_rule, "creat");
	rc |= audit_rule_syscallbyname_data(audit_rule, "truncate");
	rc |= audit_rule_syscallbyname_data(audit_rule, "execve");
	rc |= audit_rule_syscallbyname_data(audit_rule, "sendfile");

	if (rc < 0) 
		goto err;

	rc = audit_add_rule_data(rac->fd, audit_rule, flags, action);
	if (rc > 0)
		return 0;
err:
	return -1;
}

/*
 * Deletes rules from audit system (called from atexit() callback)
 */
static void
delete_rule()
{
	int rc;

	if (!audit_rule)
		return;

	debug("deleting audit rule");

	rc = audit_delete_rule_data (audit_fd, audit_rule, AUDIT_FILTER_EXIT, AUDIT_ALWAYS);

	if (rc < 0 && error_out)
		fprintf(error_out, "%s: ERROR: deleting rule (%s)\n",
				progname, strerror(-rc));

	audit_rule = NULL;
}

/*
 * Allocates new block and add it to list of blocks
 */
static RacBlock *
block_new(RacStatus *rac)
{
	RacBlock *blk = malloc(sizeof(RacBlock));

	debug("allocate new block");

	if (!blk)
		return NULL;
	memset(blk, 0, sizeof(*blk));
	blk->pos = blk->buff;

	if (!rac->b_first)
		rac->b_first = blk;
	else
		rac->b_last->next = blk;
	rac->b_last = blk;
	return blk;
}

/*
 * Adds event message at end of block
 */
#define RAC_HDR_PATH	"type=PATH msg="
#define RAC_HDR_CWD	"type=CWD msg="
#define RAC_HDR_SYSCALL	"type=SYSCALL msg="

#define RAC_IGN_CWD	"cwd=\"/\""
#define RAC_IGN_CWD_LEN	(sizeof(RAC_IGN_CWD) - 1)

static int
block_add_event(RacStatus *rac, const struct audit_reply *rep)
{
	RacBlock *blk = rac->b_last;
	int space = 0;
	char *hdr;
	int hdrlen;
	int len;

debug("block_add_event");

	if (rep->type == AUDIT_SYSCALL)
		hdr = RAC_HDR_SYSCALL;
	else if (rep->type == AUDIT_CWD) {
		/* we don't save cwd="/" */
		if (strncmp(rep->message + (rep->len - RAC_IGN_CWD_LEN),
					RAC_IGN_CWD, RAC_IGN_CWD_LEN) == 0)
			return 0;

		hdr = RAC_HDR_CWD;
	}
	else if (rep->type == AUDIT_PATH)
		hdr = RAC_HDR_PATH;
	else
		return -1;

	hdrlen = strlen(hdr);
	len = hdrlen + rep->len + 2;

	if (len > MEMBLK_SIZE)
		return  -1;
	if (blk)
		space = MEMBLK_SIZE - (blk->pos - blk->buff);
	if (space < len) {
		blk = block_new(rac);
		space = MEMBLK_SIZE;
	}
	if (!blk)
		return -1;

	debug("add new event to block (space: %d, len: %d)", space, len);

	memcpy(blk->pos, hdr, hdrlen);
	blk->pos += hdrlen;

	memcpy(blk->pos, rep->message, rep->len);
	blk->pos += rep->len;

	*blk->pos = '\n';
	blk->pos++;
	*blk->pos = '\0';

	if (space > len)
		blk->pos++;

	rac->nrecords++;

	if (rep->type == AUDIT_SYSCALL)
		rac->nevents++;

	if (has_debug && is_foreground(rac) && debug_out) {
		if (fwrite(blk->pos - len, 1, len - 1, debug_out))
			fputc('\n', debug_out);
	}

debug("block_add_event: done");

	return 0;
}

static void
blocks_free(RacStatus *rac)
{
	RacBlock *blk = rac->b_first;

	if (blk)
		debug("deallocate blocks");

	while (blk) {
		RacBlock *x = blk;
		blk = x->next;
		free(x);
	}
	rac->b_first = NULL;
	rac->b_last = NULL;
}

/*
 * Dumpa all collected data to file
 */
static int
blocks_dump(RacStatus *rac, char *filename)
{
	RacBlock *blk;
	char *p;
	FILE *f;

	if (!(f = fopen(filename, "w")))
		return -1;

	debug("dumping %d records to raw log %s", rac->nrecords, filename);

	for (blk = rac->b_first; blk; blk = blk->next) {
		for (p = blk->buff; *p && p < blk->pos; ) {
			int len = strlen(p);
			if (len)
				fprintf(f, "%s\n", p);
			p += len+1;
		}
	}
	fclose(f);
	return 0;
}



/*
 * Converts rac blocks to array of buffers
 */
static char **
blocks_to_array(RacStatus *rac)
{
	RacBlock *blk;
	char **ary, *p;
	int i = 0;

	if (!rac->nrecords)
		return NULL;

	debug("converting blocks to array");

	ary = (char **) malloc(sizeof(char *) * (rac->nrecords + 1));
	if (!ary)
		return NULL;

	for (blk = rac->b_first; blk; blk = blk->next) {
		for (p = blk->buff; *p && p < blk->pos && i < rac->nrecords; ) {
			int len = strlen(p);
			if (len)
				ary[i++] = p;
			p += len+1;
		}
	}
	return ary;
}

static int
pathcmp(const void *a, const void *b)
{
	return strcmp(*(char **) a, *(char **) b);
}

static int
blocks_dump_as_lists(RacStatus *rac, const char *filename_tpl)
{
	char **ary = NULL;
	char **all = NULL;
	int nfiles, sep;

	/* returns new allocated array of pointers to our buffers */
	ary = blocks_to_array(rac);
	if (!ary)
		return -1;

	debug("converting array of events to list of files");

	/* the 'ary' is deallocated after this call! */
	all = parse_events(rac, ary, &nfiles, &sep);

	/* we needn't it */
	free(ary);

	if (!all)
		return -1;

	if (nfiles) {
		int e = sep ? : nfiles;
		debug("sorting early list (%d/%d items)", e, nfiles);
		qsort(all, e, sizeof(char *), pathcmp);
		list_write(rac, all, e, filename_tpl, "early");
	}
	if (sep) {
		debug("sorting later list (%d/%d items)", nfiles-sep, nfiles);
		qsort(all + sep, nfiles - sep, sizeof(char *), pathcmp);
		list_write(rac, all + sep, nfiles - sep, filename_tpl, "later");
	}

	free(all);
	return 0;
}

static int
list_write(RacStatus *rac, char **list, int size, const char *filetpl, const char *fileext)
{
	int i;
	FILE *out;
	char filename[ PATH_MAX ];
	char *last = NULL;

	snprintf(filename, sizeof(filename), filetpl, fileext);
	if (!(out = fopen(filename, "w")))
		return -1;

	debug("writing list to %s", filename);

	for (i = 0; i < size; i++) {
		if (last && strcmp(last, list[i]) == 0)
			/* remove duplicates  */
			continue;
		fprintf(out, "%s\n", list[i]);
		last = list[i];
	}

	fclose(out);
	return 0;
}


static char **
parse_events(RacStatus *rac, char **ary, int *_nfiles, int *sep)
{
	char **all;
	int nfiles = 0;
	int ignlen = 0;
	int begin = 0;
	auparse_state_t *au;

	*_nfiles = *sep = 0;

	au = auparse_init(AUSOURCE_BUFFER_ARRAY, (void *) ary);
	if (!au)
		return NULL;

	debug("parsing buffers");

	/* libauparse sucks ... it reallocates (and duplicate) all buffers to
	 * internal version -- so, we deallocate our version ASAP
	 */
	blocks_free(rac);

	all = (char **) malloc(sizeof(char *) * (rac->nevents + 1));
	if (!all)
		return NULL;

	debug("parsing buffers: start (events: %d)", rac->nevents);

	do {
		/* audit uses quotation marks in auparse_find_field() result */
		char path[PATH_MAX+3];
		char cwd[PATH_MAX+3];
		int wanted = 1;

		if (auparse_first_record(au) <= 0)
			return NULL;

		*path = *cwd = '\0';

		do {
			int type = auparse_get_type(au);
			const char *p;

			if (type == AUDIT_SYSCALL &&
					(p = auparse_find_field(au, "exe"))) {
				if (exclude_file(rac->execign, p+1))
					wanted = 0;
			}
			else if (type == AUDIT_CWD &&
					(p = auparse_find_field(au, "cwd")))
				strncpy(cwd, p + 1, sizeof(cwd));
			else if (type == AUDIT_PATH &&
					(p = auparse_find_field(au, "name"))) {
				if (!strcmp("(null)", p))
					continue;
				strncpy(path, p + 1, sizeof(path));
			}

		} while(auparse_next_record(au) > 0);

		if (!*cwd)
			strcpy(cwd, "/\"");

		if (wanted && *path && *cwd) {
			char buff[PATH_MAX+2];	/* 2 is "/\0" */
			int len;
			struct stat st;

			debug("path: %s, cwd: %s", path, cwd);

			/* add terminator (..because stupid strncpy) and
			 * remove quotation marks
			 */
			path[sizeof(path)-1] = '\0';
			len = strlen(path);
			path[len - 1] = '\0';

			cwd[sizeof(cwd)-1] = '\0';
			len = strlen(cwd);
			cwd[len - 1] = '\0';

			if (!myrealpath(path, buff, sizeof(buff), cwd))
				continue;

			if (*buff != '/')
				continue;

			/*
			 * Lookup for begin of the list (if defined)
			 */
			if (begin == 0 && rac->listbgn) {
				if (strcmp(buff, rac->listbgn) == 0)
					begin = 1;
				else
					continue;
			}

			/* don't add to the list same filename like
			 * previous one -- it removes 10% of all files!
			 */
			if (nfiles && strcmp(all[nfiles-1], buff) == 0)
				continue;

			if (exclude_file(rac->excludes, buff))
				continue;

			if (stat(buff, &st) == -1 || S_ISREG(st.st_mode) == 0)
				continue;

			debug("parsing buffers: add file: %s", buff);
			all[nfiles++] = strdup(buff);

			/*
			 * Lookup for separator between early / later lists
			 */
			if (rac->listsep && *sep == 0 &&
					strcmp(buff, rac->listsep) == 0) {
				debug("parsing buffers: separator detected: %s", buff);
				*sep = nfiles;
			}
		}
	} while (auparse_next_event(au) > 0);

	debug("parsing buffers: done");

	auparse_destroy(au);

	all[nfiles] = NULL;
	*_nfiles = nfiles;
	return all;
}

/*
 * realpath(2) from util-linux
 */
static char *
myrealpath(const char *path, char *resolved_path, int maxreslth, const char *cwd)
{
	int readlinks = 0;
	char *npath;
	char link_path[PATH_MAX+1];
	int n;
	char *buf = NULL;
	int bufsz = 0;

	npath = resolved_path;

	/* If it's a relative pathname use getcwd for starters. */
	if (*path != '/') {
		int lcwd = strlen(cwd);
		memcpy(npath, cwd, maxreslth-2);
		npath += lcwd;
		if (npath[-1] != '/')
			*npath++ = '/';
	} else {
		*npath++ = '/';
		path++;
	}

	/* Expand each slash-separated pathname component. */
	while (*path != '\0') {
		/* Ignore stray "/" */
		if (*path == '/') {
			path++;
			continue;
		}
		if (*path == '.' && (path[1] == '\0' || path[1] == '/')) {
			/* Ignore "." */
			path++;
			continue;
		}
		if (*path == '.' && path[1] == '.' &&
		    (path[2] == '\0' || path[2] == '/')) {
			/* Backup for ".." */
			path += 2;
			while (npath > resolved_path+1 &&
			       (--npath)[-1] != '/')
				;
			continue;
		}
		/* Safely copy the next pathname component. */
		while (*path != '\0' && *path != '/') {
			if (npath-resolved_path > maxreslth-2) {
				errno = ENAMETOOLONG;
				goto err;
			}
			*npath++ = *path++;
		}

		/* Protect against infinite loops. */
		if (readlinks++ > MAX_READLINKS) {
			errno = ELOOP;
			goto err;
		}

		/* See if last pathname component is a symlink. */
		*npath = '\0';
		n = readlink(resolved_path, link_path, PATH_MAX);
		if (n < 0) {
			/* EINVAL means the file exists but isn't a symlink. */
			if (errno != EINVAL)
				goto err;
		} else {
			int m;

			/* Note: readlink doesn't add the null byte. */
			link_path[n] = '\0';
			if (*link_path == '/')
				/* Start over for an absolute symlink. */
				npath = resolved_path;
			else
				/* Otherwise back up over this component. */
				while (*(--npath) != '/')
					;

			/* Insert symlink contents into path. */
			m = strlen(path);

			if (!buf)
				buf = malloc(m + n + 1);
			else if (m + n + 1 > bufsz)
				buf = realloc(buf, m + n + 1);
			bufsz = m + n + 1;

			memcpy(buf, link_path, n);
			memcpy(buf + n, path, m + 1);
			path = buf;
		}
		*npath++ = '/';
	}
	/* Delete trailing slash but don't whomp a lone slash. */
	if (npath != resolved_path+1 && npath[-1] == '/')
		npath--;
	/* Make sure it's null terminated. */
	*npath = '\0';

	if (buf)
		free(buf);
	return resolved_path;
 err:
	if (buf)
		free(buf);
	return NULL;
}

/*
 * returns 1 if file should be excluded
 */
static int
exclude_file(char **list, const char *filename)
{
	char **p = list;

	for (; p && *p; p++) {
		const char *f = filename;
		char *e = *p;
		while(*f++ == *e++);
		if (*e == '\0')
			return 1;
	}
	return 0;
}
