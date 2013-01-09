###############################################################################
# OPENTHEORY MAKEFILE
# Joe Leslie-Hurd
###############################################################################

.SUFFIXES:

###############################################################################
# The default action.
###############################################################################

.PHONY: default
default: theories

###############################################################################
# Cleaning temporary files.
###############################################################################

TEMP = \
  articles/*.art \
  articles/*.thy

.PHONY: clean
clean:
	rm -f $(TEMP)

.PHONY: info-clean
info-clean:
	@echo
	@echo '+------------------+'
	@echo '| Clean everything |'
	@echo '+------------------+'
	@echo
	@$(MAKE) clean

###############################################################################
# Parametric theory interpretations.
###############################################################################

THEORY_INTERPRETATIONS = \
  theories/byte/byte-word.ml \
  theories/field/field-group.ml \
  theories/field/field-star-group.ml \
  theories/gfp/gfp-modular.ml \
  theories/group/group-abelian-monoid.ml \
  theories/group/group-mult-monoid.ml \
  theories/group/group-monoid.ml \
  theories/ring/ring-add.ml \
  theories/ring/ring-unit-group.ml \
  theories/word/word-modular.ml \
  theories/word10/word10-word.ml \
  theories/word12/word12-word.ml \
  theories/word16/word16-word.ml

theories/byte/byte-word.ml: theories/word/word.ml $(wildcard theories/word/word-*.ml)
	scripts/instantiate -r "word/byte" $< > $@

theories/field/field-group.ml: theories/group/group.ml $(wildcard theories/group/group-*.ml)
	scripts/instantiate -r "group/field" $< > $@

theories/field/field-star-group.ml: theories/group/group.ml $(wildcard theories/group/group-*.ml)
	scripts/instantiate -r "group/field_star" $< > $@

theories/gfp/gfp-modular.ml: theories/modular/modular.ml
	scripts/instantiate -r "modulus/oddprime:modular/gfp" $< > $@

theories/group/group-abelian-monoid.ml: theories/monoid/monoid-comm.ml
	scripts/instantiate -r "monoid/group" $< > $@

theories/group/group-mult-monoid.ml: theories/monoid/monoid-mult.ml
	scripts/instantiate -r "monoid/group" $< > $@

theories/group/group-monoid.ml: theories/monoid/monoid-thm.ml
	scripts/instantiate -r "monoid/group" $< > $@

theories/ring/ring-add.ml: theories/group/group-thm.ml theories/group/group-monoid.ml theories/group/group-sub.ml theories/group/group-abelian.ml $(wildcard theories/group/group-abelian-*.ml)
	scripts/instantiate -r "group/ring" theories/group/group-thm.ml theories/group/group-monoid.ml theories/group/group-sub.ml theories/group/group-abelian.ml > $@

theories/ring/ring-unit-group.ml: theories/group/group.ml $(wildcard theories/group/group-*.ml)
	scripts/instantiate -r "group/ring_unit" $< > $@

theories/word/word-modular.ml: theories/modular/modular.ml
	scripts/instantiate -r "modulus/word_size:modular/word" $< > $@

theories/word10/word10-word.ml: theories/word/word.ml $(wildcard theories/word/word-*.ml)
	scripts/instantiate -r "word/word10" $< > $@

theories/word12/word12-word.ml: theories/word/word.ml $(wildcard theories/word/word-*.ml)
	scripts/instantiate -r "word/word12" $< > $@

theories/word16/word16-word.ml: theories/word/word.ml $(wildcard theories/word/word-*.ml)
	scripts/instantiate -r "word/word16" $< > $@

.PHONY: theory-interpretations
theory-interpretations: $(THEORY_INTERPRETATIONS)

.PHONY: info-theory-interpretations
info-theory-interpretations:
	@echo
	@echo '+-------------------------------+'
	@echo '| Interpret parametric theories |'
	@echo '+-------------------------------+'
	@echo
	@$(MAKE) theory-interpretations

###############################################################################
# Extract the theories.
###############################################################################

extract-theories:
	cd .. && OPENTHEORY_LOGGING=1 opentheory/scripts/capture

info-extract-theories:
	@echo
	@echo '+------------------+'
	@echo '| Extract theories |'
	@echo '+------------------+'
	@echo
	@$(MAKE) extract-theories

###############################################################################
# Check the theory sources.
###############################################################################

THEORY_SOURCES = \
  pair.ml \
  nums.ml \
  recursion.ml \
  arith.ml \
  calc_num.ml \
  sets.ml \
  relations.ml \
  wf.ml \
  normalizer.ml \
  grobner.ml \
  ind_types.ml \
  lists.ml \
  realax.ml \
  opentheory/theories/tactics.ml \
  opentheory/theories/option/option.ml \
  opentheory/theories/list/list.ml \
  opentheory/theories/stream/stream.ml \
  opentheory/theories/probability/probability.ml \
  opentheory/theories/natural-bits/natural-bits.ml \
  opentheory/theories/natural-divides/natural-divides.ml \
  opentheory/theories/natural-gcd/natural-gcd.ml \
  opentheory/theories/natural-prime/natural-prime.ml \
  opentheory/theories/natural-fibonacci/natural-fibonacci.ml \
  opentheory/theories/monoid/monoid.ml \
  opentheory/theories/group/group.ml \
  opentheory/theories/ring.ml \
  opentheory/theories/field.ml \
  opentheory/theories/modular/modular.ml \
  opentheory/theories/gfp/gfp.ml \
  opentheory/theories/word/word.ml \
  opentheory/theories/byte/byte.ml \
  opentheory/theories/word10/word10.ml \
  opentheory/theories/word12/word12.ml \
  opentheory/theories/word16/word16.ml \
  opentheory/theories/parser/parser.ml \
  opentheory/theories/char/char.ml \
  opentheory/theories/montgomery/montgomery.ml \
  opentheory/theories/h/h.ml \
  opentheory/theories/map-reduce-bit3x3/map-reduce-bit3x3.ml \
  opentheory/theories/haskell-parser/haskell-parser.ml \
  opentheory/theories/haskell-char/haskell-char.ml \
  opentheory/theories/haskell-prime/haskell-prime.ml

check-theories:
	@echo Looking for duplicate let bindings:
	@cd .. && cat $(THEORY_SOURCES) | grep '^let ' | sort | uniq -d

info-check-theories:
	@echo
	@echo '+----------------------+'
	@echo '| Check theory sources |'
	@echo '+----------------------+'
	@echo
	@$(MAKE) check-theories

###############################################################################
# Export the theories.
###############################################################################

.PHONY: theories
theories:
	@$(MAKE) info-clean
	@$(MAKE) info-theory-interpretations
	@$(MAKE) info-extract-theories
	@$(MAKE) info-check-theories
