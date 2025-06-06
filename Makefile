# -*- Makefile -*-

######################################################################
# USAGE:                                                             #
#                                                                    #
# make all: Build the MathComp library entirely,                     #
# make test-suite: Run the test suite,                               #
# make only TGTS="...vo": Build the selected libraries of MathComp.  #
#                                                                    #
# The rules this-config::, this-build::, this-only::,                #
# this-test-suite::, this-distclean::, this-clean::  #
# and __always__:: may be extended.                                  #
#                                                                    #
# Additionally, the following variables may be customized:           #
SUBDIRS?=
COQBIN?=$(dir $(shell command -v coqtop || command -v rocq))
COQTOP=$(shell command -v coqtop || echo "$(COQBIN)rocq repl")
COQMAKEFILE?=$(shell command -v coq_makefile || echo "$(COQBIN)rocq makefile")
COQDEP?=$(COQBIN)coqdep
COQPROJECT?=_CoqProject
COQMAKEOPTIONS?=
COQMAKEFILEOPTIONS?=
V?=
VERBOSE?=V
TGTS?=
######################################################################

# local context: -----------------------------------------------------
.PHONY: all config build only test-suite test-suite-stdlib clean distclean __always__
.SUFFIXES:

H:= $(if $(VERBOSE),,@)  # not used yet
TOP     = $(dir $(lastword $(MAKEFILE_LIST)))
COQMAKE = $(MAKE) -f Makefile.coq $(COQMAKEOPTIONS)
COQMAKE_TESTSUITE = $(MAKE) -f Makefile.test-suite.coq $(COQMAKEOPTIONS)
COQMAKE_TESTSUITE_STDLIB = $(MAKE) -f Makefile.test-suite-stdlib.coq $(COQMAKEOPTIONS)
BRANCH_coq:= $(shell $(COQTOP) -v | head -1 | grep -E '(trunk|master)' \
	      | wc -l | sed 's/ *//g')

# coq version:
ifneq "$(BRANCH_coq)" "0"
COQVVV:= dev
else
COQVVV:=$(shell $(COQTOP) --print-version | cut -d" " -f1)
endif

COQV:= $(shell echo $(COQVVV) | cut -d"." -f1)
COQVV:= $(shell echo $(COQVVV) | cut -d"." -f1-2)

# export to sub- targets
export COQBIN
export COQMAKEFILE
export COQV
export COQVV
export COQVVV

# all: ---------------------------------------------------------------
all: 
	$(MAKE) config
	$(MAKE) build
	$(MAKE) test-suite

# Makefile.coq: ------------------------------------------------------

Makefile.coq: $(COQPROJECT) Makefile
	$(COQMAKEFILE) $(COQMAKEFILEOPTIONS) -f $(COQPROJECT) -o Makefile.coq

# Test suite ---------------------------------------------------------

Makefile.test-suite.coq: $(COQPROJECT).test-suite Makefile
	$(COQMAKEFILE) $(COQMAKEFILEOPTIONS) -f $(COQPROJECT).test-suite -o Makefile.test-suite.coq

# Test suite Stdlib --------------------------------------------------

Makefile.test-suite-stdlib.coq: $(COQPROJECT).test-suite-stdlib Makefile
	$(COQMAKEFILE) $(COQMAKEFILEOPTIONS) -f $(COQPROJECT).test-suite-stdlib -o Makefile.test-suite-stdlib.coq

# Global config, build, clean and distclean --------------------------
config: sub-config this-config

build: sub-build this-build

only: sub-only this-only

test-suite: sub-test-suite this-test-suite

test-suite-stdlib: sub-test-suite-stdlib this-test-suite-stdlib

clean: sub-clean this-clean

distclean: sub-distclean this-distclean

# Local config, build, clean and distclean ---------------------------
.PHONY: this-config this-build this-only this-test-suite this-test-suite-stdlib this-distclean this-clean

this-config:: __always__
	@if $$(command -v coqc >/dev/null) ; then \
	if [ -e config.stamp -a "`coqc --print-version`" = "`cat config.stamp 2>/dev/null`" ] ; then \
		echo 'already configured';\
	else\
		coqc --print-version > config.stamp;\
		echo 'configuring for ' `coqc --print-version`;\
		if (coqc --version | grep -q '8.20') ; then \
			echo '*****************************************************************';\
			echo 'old coq version detected, double check the diff before committing';\
			echo '*****************************************************************';\
			sed -i.bak -e 's/From Corelib/From Coq/' `find . -name \*.v` ; \
			sed -i.bak -e 's/IntDef/ZArith/' `find . -name \*.v` ; \
		fi;\
	fi ; fi
	# Remove all of the above when requiring Rocq >= 9.0

this-build:: this-config Makefile.coq
	+$(COQMAKE)

this-only:: this-config Makefile.coq
	+$(COQMAKE) only "TGTS=$(TGTS)"

this-test-suite:: build Makefile.test-suite.coq
	+$(COQMAKE_TESTSUITE)

this-test-suite-stdlib:: build Makefile.test-suite-stdlib.coq
	+$(COQMAKE_TESTSUITE_STDLIB)

this-distclean:: this-clean
	rm -f config.stamp
	rm -f Makefile.coq Makefile.coq.conf
	rm -f Makefile.test-suite.coq Makefile.test-suite.coq.conf
	rm -f Makefile.test-suite-stdlib.coq Makefile.test-suite-stdlib.coq.conf

this-clean:: __always__
	@if [ -f Makefile.coq ]; then $(COQMAKE) cleanall; fi
	@if [ -f Makefile.test-suite.coq ]; then $(COQMAKE_TESTSUITE) cleanall; fi
	@if [ -f Makefile.test-suite-stdlib.coq ]; then $(COQMAKE_TESTSUITE_STDLIB) cleanall; fi

# Install target -----------------------------------------------------
.PHONY: install

install: __always__ Makefile.coq
	$(COQMAKE) install

# counting lines of Coq code -----------------------------------------
.PHONY: count

COQFILES = $(shell grep '.v$$' $(COQPROJECT))

count:
	@coqwc $(COQFILES) | tail -1 | \
	  awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'
# Additionally cleaning backup (*~) files ----------------------------
this-distclean::
	rm -f $(shell find . -name '*~')

# Make in SUBDIRS ----------------------------------------------------
ifdef SUBDIRS
sub-%: __always__
	@set -e; for d in $(SUBDIRS); do $(MAKE) -C $$d $(@:sub-%=%); done
else
sub-%: __always__
	@true
endif

# Make of individual .vo ---------------------------------------------
structures.vo : %.vo: __always__ Makefile.coq
	+$(COQMAKE) $@

$(addsuffix o,$(wildcard examples/*.v examples/*/*.v tests/*.v tests/unit/*.v)): __always__ config build Makefile.test-suite.coq Makefile.test-suite-stdlib.coq
	+$(COQMAKE_TESTSUITE) $@
	+$(COQMAKE_TESTSUITE_stdlib) $@
