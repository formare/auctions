SYNC_FILES = \
	Vickrey.casl \
	README.casl.html

all: sync

sync:
	rsync -avzc --delete $(SYNC_FILES) $(DEST)

.SECONDEXPANSION:
%.tptp: $$(word 1,$$(subst _, ,$$*)).casl
	hets -n $(word 2,$(subst _, ,$*)) -o tptp -v2 $<
# example for this rule: creates Vickrey_Maximum.tptp from Vickrey.casl
