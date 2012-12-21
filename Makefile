SYNC_FILES = \
	LICENSE LICENSE-CC-BY LICENSE-ISC \
	README.html \
	.htaccess
SUBDIRS = \
	casl \
	isabelle
export DEST = gromit:/bham/htdocs/website/research/projects/formare/code/auction-theory

.PHONY: all sync subdirs force-make

all: sync subdirs

sync:
	rsync -avzc --delete $(SYNC_FILES) $(DEST)

subdirs: $(SUBDIRS)

$(SUBDIRS): force-make
	$(MAKE) -C $@


force-make:
	true
