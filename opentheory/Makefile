###############################################################################
# OPENTHEORY MAKEFILE
# Copyright (c) 2011 Joe Hurd, distributed under the MIT license
###############################################################################

.SUFFIXES:

###############################################################################
# The default action.
###############################################################################

.PHONY: default
default: example-theories

###############################################################################
# Parametric theory interpretations.
###############################################################################

THEORY_INTERPRETATIONS = \
  examples/byte-word.ml \
  examples/gfp-modular.ml \
  examples/word-modular.ml \
  examples/word10-word.ml \
  examples/word12-word.ml \
  examples/word16-word.ml

examples/byte-word.ml: examples/word.ml examples/word-modular.ml
	scripts/instantiate -r "word/byte" $< > $@

examples/gfp-modular.ml: examples/modular.ml
	scripts/instantiate -r "modulus/oddprime:modular/gfp" -x $< > $@

examples/word-modular.ml: examples/modular.ml
	scripts/instantiate -r "modulus/word_size:modular/word" -x $< > $@

examples/word10-word.ml: examples/word.ml examples/word-modular.ml
	scripts/instantiate -r "word/word10" $< > $@

examples/word12-word.ml: examples/word.ml examples/word-modular.ml
	scripts/instantiate -r "word/word12" $< > $@

examples/word16-word.ml: examples/word.ml examples/word-modular.ml
	scripts/instantiate -r "word/word16" $< > $@

.PHONY: theory-interpretations
theory-interpretations: $(THEORY_INTERPRETATIONS)

###############################################################################
# Cleaning temporary files.
###############################################################################

TEMP = \
  articles/*.art \
  articles/*.thy

.PHONY: clean
clean:
	@echo
	@echo '********************'
	@echo '* Clean everything *'
	@echo '********************'
	@echo
	rm -f $(TEMP)

###############################################################################
# The standard theory library.
###############################################################################

.PHONY: standard-theories
standard-theories:
	$(MAKE) clean
	$(MAKE) theory-interpretations
	cd .. && OPENTHEORY_STDLIB=1 opentheory/scripts/capture

###############################################################################
# Example theories.
###############################################################################

.PHONY: example-theories
example-theories:
	$(MAKE) clean
	$(MAKE) theory-interpretations
	cd .. && opentheory/scripts/capture
