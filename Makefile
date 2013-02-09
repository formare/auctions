include Makefile.vars

SYNC_FILES = \
	LICENSE LICENSE-CC-BY LICENSE-ISC \
	README.html
SUBDIRS = \
	casl \
	isabelle

.PHONY: all sync subdirs force-make

all: sync subdirs

include Makefile.in

subdirs: $(SUBDIRS)

$(SUBDIRS): force-make
	$(MAKE) -C $@


force-make:
	true
