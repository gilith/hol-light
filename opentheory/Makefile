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
  export/files.txt \
  export/log.txt \
  export/*.art \
  export/*.int \
  export/*.thy

.PHONY: clean
clean:
	rm -f $(TEMP)

.PHONY: info-clean
info-clean:
	@echo
	@echo '+-----------------------------------+'
	@echo '| Clean exported HOL Light theories |'
	@echo '+-----------------------------------+'
	@echo
	@$(MAKE) clean

###############################################################################
# Instantiate parametric proof tools.
###############################################################################

PARAMETRIC_PROOF_TOOLS = \
  theories/byte/byte-tools.ml \
  theories/word10/word10-tools.ml \
  theories/word12/word12-tools.ml \
  theories/word16/word16-word-tools.ml

theories/byte/byte-tools.ml: theories/word/word-tools.ml
	scripts/instantiate -r "word/byte" $< > $@

theories/word10/word10-tools.ml: theories/word/word-tools.ml
	scripts/instantiate -r "word/word10" $< > $@

theories/word12/word12-tools.ml: theories/word/word-tools.ml
	scripts/instantiate -r "word/word12" $< > $@

theories/word16/word16-word-tools.ml: theories/word/word-tools.ml
	scripts/instantiate -r "word/word16" $< > $@

.PHONY: instantiate-parametric-proof-tools
instantiate-parametric-proof-tools: $(PARAMETRIC_PROOF_TOOLS)

.PHONY: info-instantiate-parametric-proof-tools
info-instantiate-parametric-proof-tools:
	@echo
	@echo '+----------------------------------------------+'
	@echo '| Instantiate HOL Light parametric proof tools |'
	@echo '+----------------------------------------------+'
	@echo
	@$(MAKE) instantiate-parametric-proof-tools

###############################################################################
# Export theories.
###############################################################################

.PHONY: export-theories
export-theories:
	cd .. && opentheory/scripts/export-theories

.PHONY: info-export-theories
info-export-theories:
	@echo
	@echo '+---------------------------+'
	@echo '| Export HOL Light theories |'
	@echo '+---------------------------+'
	@echo
	@$(MAKE) export-theories

###############################################################################
# Check theory sources.
###############################################################################

.PHONY: check-theories
check-theories: export/files.txt
	@echo Looking for duplicate let bindings:
	@cd .. && (for f in $$(cat opentheory/export/files.txt) ; do cat $$f ; done) | grep '^let ' | grep -v '^let () =' | sort | uniq -d
	@echo
	@echo Looking for duplicate theorem exports:
	@cd .. && (for f in $$(cat opentheory/export/files.txt) ; do cat $$f ; done) | grep '^export_thm ' | sort | uniq -d
	@echo

.PHONY: info-check-theories
info-check-theories:
	@echo
	@echo '+--------------------------------+'
	@echo '| Check HOL Light theory sources |'
	@echo '+--------------------------------+'
	@echo
	@$(MAKE) check-theories

###############################################################################
# Export theories.
###############################################################################

.PHONY: theories
theories:
	@$(MAKE) info-clean
	@$(MAKE) info-instantiate-parametric-proof-tools
	@$(MAKE) info-export-theories
	@$(MAKE) info-check-theories

###############################################################################
# Export the tiny set of theories used to test the opentheory tool.
###############################################################################

.PHONY: prepare-tiny-theories
prepare-tiny-theories:
	perl -ne 'BEGIN: { my $$done = 0; } if (!$$done) { print "$$_"; chomp; if ($$_ =~ m{opentheory/load[.]ml}) { print "Export.debug_export_thm_enable := false;;\n"; } elsif ($$_ =~ /drule[.]ml/) { print "loads \"opentheory/theories/tiny/tiny.ml\";;\n"; $$done = 1; } }' < ../hol.ml > theories/tiny/hol.ml

.PHONY: info-prepare-tiny-theories
info-prepare-tiny-theories:
	@echo
	@echo '+-----------------------+'
	@echo '| Prepare tiny theories |'
	@echo '+-----------------------+'
	@echo
	@$(MAKE) prepare-tiny-theories

.PHONY: export-tiny-theories
export-tiny-theories:
	cd .. && echo '#use "opentheory/theories/tiny/hol.ml";;' | ocaml >opentheory/theories/tiny/log.txt 2>&1
	if grep '^Exception:\|^Error:\|^Error in included file\|Warning: inventing type variables' theories/tiny/log.txt ; then cat theories/tiny/log.txt ; exit 1 ; fi

.PHONY: info-export-tiny-theories
info-export-tiny-theories:
	@echo
	@echo '+----------------------+'
	@echo '| Export tiny theories |'
	@echo '+----------------------+'
	@echo
	@$(MAKE) export-tiny-theories

.PHONY: tiny-theories
tiny-theories:
	@$(MAKE) info-clean
	@$(MAKE) info-prepare-tiny-theories
	@$(MAKE) info-export-tiny-theories
