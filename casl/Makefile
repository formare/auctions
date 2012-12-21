SYNC_FILES = \
	Vickrey.casl \
	README.casl.html

all: sync

sync:
	rsync -avzc --delete $(SYNC_FILES) $(DEST)
