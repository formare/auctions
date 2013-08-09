PREFIX = .
include Makefile.vars

SYNC_FILES = \
	$(LICENSE_FILES)
SUBDIRS = \
	casl \
	isabelle \
	mizar \
	theorema

.PHONY: all sync subdirs force-make

all: sync subdirs

include Makefile.in
# TODO CL: on this level, prevent ZIP file from being created, or really create an all-ATT ZIP
