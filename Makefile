PREFIX = .
include Makefile.vars

SUBDIRS = \
	casl \
	isabelle \
	mizar \
	theorema

.PHONY: all sync subdirs force-make

all: sync subdirs

include Makefile.in
