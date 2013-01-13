include ../Makefile.vars
include ../Makefile.in

SYNC_FILES = \
	Vickrey.casl \
	README.casl.html

all: sync

.SECONDEXPANSION:
%: $$(word 1,$$(subst _, ,$$*)).casl
	hets -n $(word 1,$(subst ., ,$(word 2,$(subst _, ,$*)))) -o $(word 2,$(subst ., ,$*)) -v2 $<
# example for this rule: creates Vickrey_Maximum.tptp from Vickrey.casl

# Output includes all imported stuff as axioms
# could additionally use -t to specify translation/comorphism to be used
