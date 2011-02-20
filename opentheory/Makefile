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
# Parametric theory instantiations.
###############################################################################

THEORY_INSTANTIATIONS = \
  examples/byte-word.ml \
  examples/word-modular.ml \
  examples/word16-word.ml

examples/byte-word.ml: examples/word.ml examples/word-modular.ml
	scripts/instantiate -r "word/byte" $< > $@

examples/word-modular.ml: examples/modular.ml
	scripts/instantiate -r "modulus/word_size:modular/word" -x $< > $@

examples/word16-word.ml: examples/word.ml examples/word-modular.ml
	scripts/instantiate -r "word/word16" $< > $@

.PHONY: theory-instantiations
theory-instantiations: $(THEORY_INSTANTIATIONS)

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
	cd .. && OPENTHEORY_STDLIB=1 opentheory/scripts/capture

###############################################################################
# Example theories.
###############################################################################

.PHONY: example-theories
example-theories:
	$(MAKE) clean
	$(MAKE) theory-instantiations
	cd .. && opentheory/scripts/capture
