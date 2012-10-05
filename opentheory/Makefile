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
# Parametric theory interpretations.
###############################################################################

THEORY_INTERPRETATIONS = \
  theories/byte/byte-word.ml \
  theories/field-group.ml \
  theories/field-star-group.ml \
  theories/gfp/gfp-modular.ml \
  theories/word/word-modular.ml \
  theories/word10-word.ml \
  theories/word12-word.ml \
  theories/word16-word.ml

theories/byte/byte-word.ml: theories/word/word.ml theories/word/word-modular.ml
	scripts/instantiate -r "word/byte" $< > $@

theories/field-group.ml: theories/group/group.ml
	scripts/instantiate -r "group/field" $< > $@

theories/field-star-group.ml: theories/group/group.ml
	scripts/instantiate -r "group/field_star" $< > $@

theories/gfp/gfp-modular.ml: theories/modular/modular.ml
	scripts/instantiate -r "modulus/oddprime:modular/gfp" $< > $@

theories/word/word-modular.ml: theories/modular/modular.ml
	scripts/instantiate -r "modulus/word_size:modular/word" $< > $@

theories/word10-word.ml: theories/word/word.ml theories/word/word-modular.ml
	scripts/instantiate -r "word/word10" $< > $@

theories/word12-word.ml: theories/word/word.ml theories/word/word-modular.ml
	scripts/instantiate -r "word/word12" $< > $@

theories/word16-word.ml: theories/word/word.ml theories/word/word-modular.ml
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
# Export the theories.
###############################################################################

.PHONY: theories
theories:
	$(MAKE) clean
	$(MAKE) theory-interpretations
	cd .. && OPENTHEORY_LOGGING=1 opentheory/scripts/capture
