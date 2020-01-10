include $(top_srcdir)/config/include-Makefile.am

sbin_PROGRAMS = readahead-collector readahead
dist_sysconf_DATA = readahead.conf


readahead_SOURCES = readahead.c nls.h

readahead_LDADD = -lext2fs -lblkid
readahead_collector_LDADD = -laudit -lauparse

