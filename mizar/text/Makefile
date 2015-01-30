TOOLS = ../tools

# call with "make vickrey-de-bruijn.miz"
%-de-bruijn.miz: %.miz
	$(TOOLS)/onlycode.sh < $< > $@

%-proofless.miz: %.miz
	$(TOOLS)/proofcut.sh < $< > $@
