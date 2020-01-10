AC_INIT(readahead, 1.5.6, harald@redhat.com)

AC_PREREQ(2.59)

AC_CONFIG_AUX_DIR(config)

AM_INIT_AUTOMAKE([check-news -Wall foreign 1.9 dist-bzip2])

AC_CONFIG_SRCDIR(src/readahead.c)

AM_GNU_GETTEXT_VERSION([0.17])
AM_GNU_GETTEXT([external])

AC_PREFIX_DEFAULT([/usr])

# Check whether exec_prefix=/usr:
case $exec_prefix:$prefix in
NONE:NONE | NONE:/usr | /usr:*)
  AC_MSG_NOTICE([Default --exec-prefix detected.])
  case $bindir in
  '${exec_prefix}/bin') bindir=/bin
    AC_MSG_NOTICE([  --bindir defaults to /bin]) ;;
  esac
  case $sbindir in
  '${exec_prefix}/sbin') sbindir=/sbin
    AC_MSG_NOTICE([  --sbindir defaults to /sbin]) ;;
  esac ;;
esac

# Check whether prefix=/usr:
case $prefix in
NONE | /usr )
  case $sysconfdir in
  '${prefix}/etc') sysconfdir=/etc
    AC_MSG_NOTICE([  --sysconfdir defaults to /etc]) ;;
  esac ;;
esac

AC_PROG_CC_STDC
AC_PROG_RANLIB

AC_SYS_LARGEFILE

AC_CHECK_LIB(blkid, blkid_devno_to_devname)
AC_CHECK_LIB(ext2fs, ext2fs_open)
AC_CHECK_LIB(audit, audit_open)
AC_CHECK_LIB(auparse, auparse_init)

AC_CHECK_MEMBER([struct auditd_reply_list.reply], [AC_DEFINE(HAVE_AUDITD_REPLY_LIST, 1,
       [Define if libaudit.h defines struct auditd_reply_list.])], [], [#include <libaudit.h>])

     

AC_CONFIG_HEADERS(config.h)

LIBS=""

AC_CONFIG_FILES([
Makefile
src/Makefile
scripts/Makefile
lists/Makefile
po/Makefile.in
])

AC_OUTPUT
