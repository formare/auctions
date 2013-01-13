include Makefile.vars
include Makefile.in

SYNC_FILES = \
	LICENSE LICENSE-CC-BY LICENSE-ISC \
	README.html \
	.htaccess
SUBDIRS = \
	casl \
	isabelle

.PHONY: all sync subdirs force-make

all: sync subdirs

subdirs: $(SUBDIRS)

$(SUBDIRS): force-make
	$(MAKE) -C $@


force-make:
	true
