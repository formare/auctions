PREFIX = ..
include $(PREFIX)/Makefile.vars

all: sync

# CL: trying to prevent (but doesn't work) that this is misinterpreted as "make Vickrey_SecondPriceAuction.tptp".  Per-goal TPTP files cannot yet be created automatically.
Vickrey_SecondPriceAuction_only_max_bidder_wins.tptp: Vickrey.casl

include $(PREFIX)/Makefile.in

.SECONDEXPANSION:
%: $$(word 1,$$(subst _, ,$$*)).casl
	hets -n $(word 1,$(subst ., ,$(word 2,$(subst _, ,$*)))) -o $(word 2,$(subst ., ,$*)) -v2 $<
# example for this rule: creates Vickrey_Maximum.tptp from Vickrey.casl

# Output includes all imported stuff as axioms
# could additionally use -t to specify translation/comorphism to be used
