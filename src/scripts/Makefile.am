include $(top_srcdir)/config/include-Makefile.am

dnl sysconfrcdir = $(sysconfdir)/rc.d/init.d
dnl dist_sysconfrc_SCRIPTS = readahead_early readahead_later

sysconfcrondir = $(sysconfdir)/cron.daily
dist_sysconfcron_SCRIPTS = readahead.cron

sysconfcronmonthlydir = $(sysconfdir)/cron.monthly
dist_sysconfcronmonthly_SCRIPTS = readahead-monthly.cron

initdir = $(sysconfdir)/init
dist_init_DATA = readahead-collector.conf readahead-disable-services.conf readahead.conf
