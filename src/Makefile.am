include $(top_srcdir)/config/include-Makefile.am

SUBDIRS = src \
	po \
	scripts \
	lists

ACLOCAL_AMFLAGS = -I m4

EXTRA_DIST = 	README \
		po/update-potfiles

dist_sysconfsysconf_DATA = readahead
sysconfsysconfdir = $(sysconfdir)/sysconfig

distclean-local:
	-find . -name \*~ -o -name \*.orig -o -name \*.rej | xargs rm -f
	rm -rf autom4te.cache


rpm-lists-rebuild:
	make -C lists rpm-lists-rebuild
