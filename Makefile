PREFIX = .
DPATH = .
include Makefile.vars

SYNC_FILES = \
	LICENSE LICENSE-CC-BY LICENSE-ISC \
	index.php \
	sidebar.php
SUBDIRS = \
	casl \
	isabelle #\
#	mizar

.PHONY: all sync subdirs force-make

all: sync subdirs

include Makefile.in

subdirs: $(SUBDIRS)

$(SUBDIRS): force-make
	$(MAKE) -C $@

force-make:
	true
