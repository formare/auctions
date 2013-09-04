PREFIX = .
include Makefile.vars

LICENSE_FILES := $(LICENSE_FILES:README=README.md) LICENSE LICENSE-CC-BY LICENSE-ISC

SUBDIRS = \
	casl \
	isabelle \
	mizar \
	theorema

.PHONY: all sync subdirs force-make

all: sync subdirs

include Makefile.in
