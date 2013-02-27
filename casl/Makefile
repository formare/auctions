PREFIX = ..
include $(PREFIX)/Makefile.vars

SYNC_FILES = \
	Vickrey.casl \
	Vickrey-consistency.hpf \
	Vickrey-SecondPriceAuction-second_price_auction_loser_payoff.hpf \
	Vickrey-SecondPriceAuction-second_price_auction_winner_payoff.hpf \
	Vickrey-SecondPriceAuction-winners_payoff_on_deviation_from_valuation.hpf \
	Vickrey-Vickrey-vickreyA.hpf
	index.php \
	sidebar.php

all: sync

include $(PREFIX)/Makefile.in

.SECONDEXPANSION:
%: $$(word 1,$$(subst _, ,$$*)).casl
	hets -n $(word 1,$(subst ., ,$(word 2,$(subst _, ,$*)))) -o $(word 2,$(subst ., ,$*)) -v2 $<
# example for this rule: creates Vickrey_Maximum.tptp from Vickrey.casl

# Output includes all imported stuff as axioms
# could additionally use -t to specify translation/comorphism to be used
