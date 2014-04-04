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
# Building using Icarus Verilog: http://iverilog.icarus.com/
###############################################################################

IVERILOG = iverilog

VVP = vvp

TARGETS = \
  counter_91_testbench.out \
  montgomery_reduce_91_testbench.out \
  montgomery_91_testbench.out \
  double_exp_91_testbench.out

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
	$(IVERILOG) -DSEED=$(shell date +%s) -o $@ $<
