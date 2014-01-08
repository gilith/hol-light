###############################################################################
# OPENTHEORY VERILOG MAKEFILE
# Joe Leslie-Hurd
###############################################################################

.SUFFIXES:

###############################################################################
# The default action.
###############################################################################

.PHONY: default
default: iverilog

###############################################################################
# Cleaning temporary files.
###############################################################################

TEMP = \
  *.out \
  *.o

.PHONY: clean
clean:
	@echo
	@echo '+------------------+'
	@echo '| Clean everything |'
	@echo '+------------------+'
	@echo
	rm -f $(TEMP)

###############################################################################
# Building using Icarus Verilog.
###############################################################################

IVERILOG = iverilog

VVP = vvp

TARGETS = \
  counter91_testbench.out

.PHONY: iverilog-info
iverilog-info:
	@echo
	@echo '+-------------------------------------+'
	@echo '| Build and test the verilog examples |'
	@echo '+-------------------------------------+'
	@echo

.PHONY: iverilog
iverilog: iverilog-info $(TARGETS)

%.out: %.o
	$(VVP) $< | tee $@

%.o: %.v
	$(IVERILOG) -o $@ $<
