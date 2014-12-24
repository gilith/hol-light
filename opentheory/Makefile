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
  theories/gfp/gfp-modular.ml \
  theories/word/word-modular.ml \
  theories/word10/word10-word.ml \
  theories/word12/word12-word.ml \
  theories/word16/word16-word.ml
#  theories/field/field-group.ml \
#  theories/field/field-star-group.ml \
#  theories/group/group-abelian-monoid.ml \
#  theories/group/group-mult-monoid.ml \
#  theories/group/group-monoid.ml \
#  theories/ring/ring-add-comm.ml \
#  theories/ring/ring-add-group.ml \
#  theories/ring/ring-mult.ml \
#  theories/ring/ring-unit-group.ml \

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

theories/ring/ring-add-group.ml: theories/group/group-thm.ml theories/group/group-monoid.ml theories/group/group-sub.ml
	scripts/instantiate -r "group/ring" theories/group/group-thm.ml theories/group/group-monoid.ml theories/group/group-sub.ml > $@

theories/ring/ring-add-comm.ml: theories/group/group-abelian.ml $(wildcard theories/group/group-abelian-*.ml)
	scripts/instantiate -r "group/ring" theories/group/group-abelian.ml > $@

theories/ring/ring-mult.ml: theories/monoid/monoid-thm.ml theories/monoid/monoid-mult.ml
	scripts/instantiate -r "monoid_mult_right_zero/monoid_mult_right_ZERO:monoid_mult_right_add/monoid_mult_right_ADD:monoid_mult_right_mult/monoid_mult_right_MULT:monoid/ring:mult/exp:add/mult:zero/one:ZERO/zero:ADD/add:MULT/mult" theories/monoid/monoid-thm.ml theories/monoid/monoid-mult.ml > $@

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

.PHONY: extract-theories
extract-theories:
	cd .. && OPENTHEORY_LOGGING=1 opentheory/scripts/capture

.PHONY: info-extract-theories
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

.PHONY: check-theories
check-theories: files
	@echo Looking for duplicate let bindings:
	@cd .. && (for f in $$(cat opentheory/files) ; do cat $$f ; done) | grep '^let ' | sort | uniq -d
	@echo
	@echo Looking for duplicate theorem exports:
	@cd .. && (for f in $$(cat opentheory/files) ; do cat $$f ; done) | grep '^export_thm ' | sort | uniq -d
	@echo

.PHONY: info-check-theories
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

###############################################################################
# Extract the tiny set of theories used to test the opentheory tool.
###############################################################################

.PHONY: prepare-tiny-theories
prepare-tiny-theories:
	perl -ne 'BEGIN: { my $$done = 0; } if (!$$done) { print "$$_"; chomp; if ($$_ =~ /opentheory[.]ml/) { print "Export.debug_export_thm_enable := false;;\n"; } elsif ($$_ =~ /drule[.]ml/) { print "loads \"opentheory/tiny/tiny.ml\";;\n"; $$done = 1; } }' < ../hol.ml > tiny/hol.ml

.PHONY: info-prepare-tiny-theories
info-prepare-tiny-theories:
	@echo
	@echo '+-----------------------+'
	@echo '| Prepare tiny theories |'
	@echo '+-----------------------+'
	@echo
	@$(MAKE) prepare-tiny-theories

.PHONY: extract-tiny-theories
extract-tiny-theories:
	cd .. && echo '#use "opentheory/tiny/hol.ml";;' | ocaml >opentheory/tiny/log 2>&1
	if grep '^Exception:\|^Error:\|^Error in included file\|Warning: inventing type variables' tiny/log ; then cat tiny/log ; exit 1 ; fi

.PHONY: info-extract-tiny-theories
info-extract-tiny-theories:
	@echo
	@echo '+-----------------------+'
	@echo '| Extract tiny theories |'
	@echo '+-----------------------+'
	@echo
	@$(MAKE) extract-tiny-theories

.PHONY: tiny-theories
tiny-theories:
	@$(MAKE) info-clean
	@$(MAKE) info-prepare-tiny-theories
	@$(MAKE) info-extract-tiny-theories
