
/*
 * readahead -- read in advance a list of files, adding them to the page cache
 *
 * Copyright (C) 2005 Ziga Mahkovec <ziga.mahkovec@klika.si>
 *
 * Copyright (C) 2006,2007  Red Hat, Inc.
 * Karel Zak <kzak@redhat.com>
 *
 * Based on a previous version by Arjan van de Ven  <arjanv@redhat.com>
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

#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/syscall.h>
#include <ext2fs/ext2fs.h>
#include <blkid/blkid.h>
#include <getopt.h>
#include <locale.h>
#include <limits.h>
#include "nls.h"

static inline int ioprio_set(int which, int who, int ioprio)
{
        return syscall(SYS_ioprio_set, which, who, ioprio);
}

#define IOPRIO_WHO_PROCESS 1
#define IOPRIO_CLASS_IDLE 3
#define IOPRIO_CLASS_SHIFT 13
#define IOPRIO_IDLE_LOWEST (7 | (IOPRIO_CLASS_IDLE << IOPRIO_CLASS_SHIFT))

#define MAXFILES	32768
#define MAXDEVICES	32

/* Block group hit threshold (triggering complete inode table scan) */
#define GROUP_HIT_THRESH  128

#define IO_MGR	unix_io_manager

#define TIMEDIFF(t1, t2) ((t2.tv_sec-t1.tv_sec) * 1000 + \
			  (t2.tv_usec-t1.tv_usec) / 1000)

static char *progname;
static int verbose;
static int timing;
static long int maxsize;

/* Modes */
#define MODE_FULL	1
#define MODE_SORT	2
#define MODE_FAST	3

struct device {
	dev_t		st_dev;
	char		*name;
	ext2_filsys	fs;
	blk_t		*group_hits;
};

struct file {
	char*	path;
	off_t	size;
	blk_t	block;
};

/* Compare files by path. */
static int
comp_files_path(const void *f1, const void *f2)
{
	struct file *fb1 = (struct file *)f1;
	struct file *fb2 = (struct file *)f2;
	return (strcmp(fb1->path, fb2->path));
}

/* Compare files by first block. */
static int
comp_files_block(const void *f1, const void *f2)
{
	struct file *fb1 = (struct file *)f1;
	struct file *fb2 = (struct file *)f2;
	return (int)(fb1->block - fb2->block);
}

/* Get the device the specified file is on. */
struct device *
get_file_device(dev_t dev, struct device *devices, int *count)
{
	int		i;
	ext2_filsys 	fs = NULL;

	for (i=0; i<*count; i++) {
		if (devices[i].st_dev == dev)
			return &devices[i];
	}
	/* Create new device */
	if (*count == MAXDEVICES) {
		fprintf(stderr, _("%s: error: max device count reached.\n"), progname);
		return NULL;
	}
	devices[i].st_dev = dev;
	devices[i].name = blkid_devno_to_devname(dev);
        if (!devices[i].name)
                return NULL;
	if (ext2fs_open(devices[i].name, 0, 0, 0, IO_MGR, &fs) || !fs)
		return NULL;
	else {
		unsigned int j, n_groups;
		devices[i].fs = fs;
		n_groups = fs->super->s_blocks_count /
			   fs->super->s_blocks_per_group + 1;
		devices[i].group_hits =
			(blk_t *)malloc(sizeof(blk_t) * n_groups);
		for (j=0; j<n_groups; j++)
			devices[i].group_hits[j] = 0;
		(*count)++;
		return &devices[i];
	}
}

/* Get the first data block of the specified file. */
int
get_first_block(ext2_filsys fs, blk_t *blocknr, e2_blkcnt_t blockcnt,
		blk_t ref_block, int ref_offset, void *private)
{
	struct file* f = (struct file *)private;
	f->block = *blocknr;
	return BLOCK_ABORT;
}

/* Read the entire inode table of the specified block group. */
void
preload_inodes(ext2_filsys fs, int group)
{
	ext2_inode_scan		e2iscan = NULL;
	struct ext2_inode	inode;
	ext2_ino_t		ino = 0;
	int			c_group;

	if (ext2fs_open_inode_scan(fs, 0, &e2iscan) || !e2iscan) {
		fprintf(stderr, _("%s: error: ext2fs_open_inode_scan failed\n"),
			       	progname);
		return;
	}
	if (ext2fs_inode_scan_goto_blockgroup(e2iscan, group)) {
		fprintf(stderr, _("%s: error: ext2fs_open_inode_scan() failed\n"),
				progname);
		ext2fs_close_inode_scan(e2iscan);
		return;
	}

	c_group = group;
	while (c_group == group &&
		!ext2fs_get_next_inode(e2iscan, &ino, &inode)) {
		c_group = ext2fs_group_of_ino(fs, ino);
	}
	ext2fs_close_inode_scan(e2iscan);
}

static int
list_new(struct file *files, char **lists, int nlists, int withsize)
{
	char buf[PATH_MAX];
	int nfiles = 0, i;
	struct timeval  t1, t2;

	if (timing && verbose)
		gettimeofday(&t1, NULL);

	for (i = 0; i < nlists; i++) {
		FILE *fin = fopen(lists[i], "r");
		if (fin == NULL) {
			fprintf(stderr, _("%s: error: %s: %s\n"),
					progname, lists[i], strerror(errno));
			continue;
		}
		while (fgets(buf, PATH_MAX, fin) != NULL) {
			struct file *file = files+nfiles;
			char *path;
			int len;

			if (!*buf)
				continue;	/* empty */
			if (*buf == '#')
				continue;	/* comment */

			if (withsize) {
				file->size = (off_t) strtoll(buf, &path, 10);
				if (*path != ' ') {
					fprintf(stderr, _("%s: error: %s: "
						"unexpected format of sorted file\n"),
						progname, lists[i]);
					return -1;
				}
				path++;
			}
			else {
				path = buf;
				files->size = 0;
			}

			len = strlen(path);
			if (path[len - 1] == '\n')
				path[--len] = '\0';
			file->path = (char *) malloc(sizeof(char) * (len + 1));
			strcpy(file->path, path);
			files->block = -1;
			nfiles++;
			if (nfiles == MAXFILES) {
				fprintf(stderr,
					_("%s: error: max file count reached\n"),
					progname);
				i = nlists;
				break;
			}
		}
		fclose(fin);
	}
	if (timing && verbose)  {
		gettimeofday(&t2, NULL);
		fprintf(stderr, _("Time (read lists): %ld ms\n"),
				TIMEDIFF(t1, t2));
	}
	if (verbose)
		fprintf(stderr, _("Create list with %d files\n"), nfiles);

	return nfiles;
}

static void
list_destroy(struct file *files, int nfiles)
{
	int i;
	for (i = 0; i < nfiles; i++)
		free(files[i].path);
	return;
}

static void
list_sort_by_paths(struct file *files, int nfiles)
{
	qsort(files, nfiles, sizeof(struct file), comp_files_path);
}

static void
list_read_blocks(struct file *files, int nfiles)
{
	int 		i;
	struct file 	*file, *last = NULL;
	off_t 		total = 0;
	int		fd = -1;
	int		fcount = 0;
	struct stat	st;
	struct device   devices[MAXDEVICES];
	int		ndevices = 0;
	struct timeval  t1, t2;

	if (timing && verbose)
		gettimeofday(&t1, NULL);

	for (i = 0, file = files; i < nfiles; i++, file++) {
		struct device *dev;
		int group;

		if (fd != -1) {
			close(fd);
			fd = -1;
		}
		if (file == NULL || file->path == NULL)
			continue;
		if (last && strcmp(file->path, last->path)==0)
			continue;		/* duplicate file */
		last = file;
#ifdef O_NOATIME
		fd = open(file->path, O_RDONLY | O_NOATIME);
		if (fd < 0)
		    fd = open(file->path, O_RDONLY);
#else
		fd = open(file->path, O_RDONLY);
#endif
		if (fd < 0 || fstat(fd, &st) < 0)
			continue;		/* open() or stat() failed */
		if (!S_ISREG(st.st_mode))
			continue;		/* not regular file */
		if (!gnu_dev_major(st.st_dev))
			continue;		/* mounted over NFS */
		if (st.st_size == 0 || (maxsize >= 0 && st.st_size > (maxsize*1024)))
			continue;		/* empty or too big file */
		file->size = st.st_size;
		dev = get_file_device(st.st_dev, devices, &ndevices);

		if (dev == NULL || dev->fs == NULL)
			continue;		/* no dev? */
		group = ext2fs_group_of_ino(dev->fs, st.st_ino);

		if (dev->group_hits[group] == GROUP_HIT_THRESH)
			preload_inodes(dev->fs, group);

		dev->group_hits[group]++;

		/* Store the first data block (for sorting later) */
		ext2fs_block_iterate2(dev->fs, st.st_ino, 0, NULL,
				      get_first_block, (void *)file);

		fcount++; /* number of really loaded files */
		total += file->size;
	}
	if (fd != -1)
		close(fd);

	for (i = 0; i < ndevices; i++) {
		if (devices[i].name)
			free(devices[i].name);
		if (devices[i].group_hits)
			free(devices[i].group_hits);
		if (devices[i].fs)
			ext2fs_close(devices[i].fs);
	}
	if (timing && verbose)  {
		gettimeofday(&t2, NULL);
		fprintf(stderr, _("Time (read blocks): %ld ms\n"),
				TIMEDIFF(t1, t2));
	}
	if (verbose)
		fprintf(stderr, _("Read blocks for %d/%d files (%llu KB)\n"),
				fcount, nfiles,
				(unsigned long long int) total / 1024);
}

static void
list_sort_by_blocks(struct file *files, int nfiles)
{
	qsort(files, nfiles, sizeof(struct file), comp_files_block);
}

static void
list_do_readahead(struct file *files, int nfiles)
{
	int		i;
	struct file	*file;
	int		fd = -1;
	struct timeval  t1, t2;
	off_t           total = 0;
	int		fcount = 0;

	if (timing && verbose)
		gettimeofday(&t1, NULL);

	for (i = 0, file = files; i < nfiles; i++, file++) {
		if (file == NULL || file->path == NULL || file->size == 0)
			continue;
#ifdef O_NOATIME
		if ((fd = open(file->path, O_RDONLY | O_NOATIME)) != -1
		    || (fd = open(file->path, O_RDONLY)) != -1) {
#else
		if ((fd = open(file->path, O_RDONLY)) != -1) {
#endif
			readahead(fd, 0, file->size);
			close(fd);
			total += file->size;
			fcount++; /* number of really loaded files */
		}
	}
	if (timing && verbose) {
		gettimeofday(&t2, NULL);
		fprintf(stderr, _("Time (readahead): %ld ms\n"), TIMEDIFF(t1, t2));
	}
	if (verbose)
		fprintf(stderr, _("Preload %d/%d files (%llu KB)\n"),
				fcount, nfiles,
				(unsigned long long int) total / 1024);
}

static int
list_write(struct file *files, int nfiles, const char *output)
{
	int		i;
	struct file	*file;
	FILE		*out = stdout;

	if (output && (out = fopen(output, "w")) == NULL) {
		fprintf(stderr, _("%s: error: %s: %s\n"),
				progname, output, strerror(errno));
		return -1;
	}
	for (i = 0, file = files; i < nfiles; i++, file++) {
		if (file == NULL || file->path == NULL || file->size == 0)
			continue;
		fprintf(out, "%llu %s\n", (unsigned long long int) file->size, file->path);
	}

	if (output)
		fclose(out);

	return 0;
}

static void
usage(int excode)
{
	fprintf(stdout, _("\n%s [options] <file> [...]\n\n"), progname);
	fputs(_("  -s | --sort            sort list of files only\n"
	      "  -o | --output <file>   output sorted list of files\n"
	      "  -d | --dont-sort       call readahead(2) for already sorted list\n"
	      "  -h | --help            this help\n"
	      "  -v | --verbose         verbose mode\n"
	      "  -t | --timing          report wasted time\n"
	      "  -m | --maxsize <10240> max size of a file to be preloaded (in KiB)\n"
	      "\n"), stdout);

	exit(excode);
}

int
main(int argc, char **argv)
{
	int i, mode = MODE_FULL;
	int res = 0;
	char *p, *output = NULL;
	struct option opts[] =
	{
		{ "sort",	0, 0, 's' },
		{ "dont-sort",  0, 0, 'd' },
		{ "help",       0, 0, 'h' },
		{ "output",     1, 0, 'o' },
		{ "verbose",    0, 0, 'v' },
		{ "timing",     0, 0, 't' },
		{ "maxsize",    1, 0, 'm' },
		{ NULL,		0, 0, 0 }
	};
	struct timeval  t1, t2;
	struct file     files[MAXFILES];
	int		nfiles = 0;

	maxsize = 10240;

	setlocale(LC_MESSAGES, "");
	bindtextdomain(PACKAGE, LOCALEDIR);
	textdomain(PACKAGE);

	progname = argv[0];
	if ((p = strrchr(argv[0], '/')))
		progname = p+1;

	while((i = getopt_long(argc, argv, "dho:stvm:", opts, NULL)) != -1) {
		switch(i) {
		case 'd':
			mode = MODE_FAST;
			break;
		case 'o':
			output = strdup(optarg);
			break;
		case 'h':
			usage(EXIT_SUCCESS);
		case 's':
			mode = MODE_SORT;
			break;
		case 't':
			timing = 1;
		case 'v':
			verbose = 1;
			break;
		case 'm':
			maxsize = strtol(optarg, NULL, 10);
			break;
		default:
			usage(EXIT_FAILURE);
		}
	}

	if (timing)
		gettimeofday(&t1, NULL);

	argc -= optind;
	argv += optind;

	if (!argv[0])
		usage(EXIT_FAILURE);

	if (verbose) {
		fprintf(stderr, _("Mode: %s\n"),
				mode == MODE_FULL ? "full" :
				mode == MODE_FAST ? "fast" : "sort" );
		if (output)
			fprintf(stderr, _("Output: %s\n"), output);
		for (i = 0; i < argc; i++)
			fprintf(stderr, _("List: %s\n"), argv[i]);
	}


	if (ioprio_set(IOPRIO_WHO_PROCESS, getpid(),
		    IOPRIO_IDLE_LOWEST) == -1)
		perror("Can not set IO priority to idle class");

	if ((nfiles = list_new(files, argv, argc, mode == MODE_FAST)) < 0) {
		free(output);
		return EXIT_FAILURE;
	}

	if (!nfiles) {
		free(output);
		return EXIT_SUCCESS;	/* empty list is not error */
	}

	if (mode == MODE_FULL || mode == MODE_SORT)
		list_sort_by_paths(files, nfiles);

	if (mode == MODE_FULL || mode == MODE_SORT)
		list_read_blocks(files, nfiles);

	if (mode == MODE_FULL || mode == MODE_SORT)
		list_sort_by_blocks(files, nfiles);

	if (mode == MODE_FULL || mode == MODE_FAST)
		list_do_readahead(files, nfiles);

	else if (mode == MODE_SORT)
		res = list_write(files, nfiles, output);

	list_destroy(files, nfiles);

	if (timing) {
		gettimeofday(&t2, NULL);
		fprintf(stderr, _("Time total: %ld ms\n"), TIMEDIFF(t1, t2));
	}
	free(output);
	exit( res == 0 ? EXIT_SUCCESS : EXIT_FAILURE );
}

