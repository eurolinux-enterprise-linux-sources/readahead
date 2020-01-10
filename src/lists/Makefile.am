include $(top_srcdir)/config/include-Makefile.am

EXTRA_DIST = README.lists default.early default.later

sysconflistsdir = $(localstatedir)/lib/readahead

#
# make rpm-lists-rebuild FILES="default.early default.later" RPM_ARCH=x86_64 RPM_LIB=lib64
#
# special case for RPM based distributions to convert lists
# from arch independent to arch specific format
rpm-lists-rebuild:
	for f in $(FILES); do \
		sed 's|%{_lib}|$(RPM_LIB)|g; s|%{_arch}|$(RPM_ARCH)|g' < $$f > $$f.tmp ; \
		mv $$f.tmp $$f ; \
	done
