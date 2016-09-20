#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.4pl6     ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f _CoqProject -o Makefile 
#

include CompCert/Makefile.menhir
comma:= ,
empty:=
space:= $(empty) $(empty)
MENHIR_INCLUDES:= $(subst $(space),$(comma),$(MENHIR_INCLUDES))

.DEFAULT_GOAL := all

# 
# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.

# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

COQLIBS?=-R . Rustre\
  -exclude-dir CompCert\
  -R CompCert/cparser compcert.cparser\
  -R CompCert/exportclight compcert.exportclight\
  -R CompCert/flocq compcert.flocq\
  -R CompCert/driver compcert.driver\
  -R CompCert/cfrontend compcert.cfrontend\
  -R CompCert/backend compcert.backend\
  -R CompCert/ia32 compcert.ia32\
  -R CompCert/common compcert.common\
  -R CompCert/lib compcert.lib\
  -exclude-dir extraction/CompCert\

COQDOCLIBS?=-R . Rustre\
  -R CompCert/cparser compcert.cparser\
  -R CompCert/exportclight compcert.exportclight\
  -R CompCert/flocq compcert.flocq\
  -R CompCert/driver compcert.driver\
  -R CompCert/cfrontend compcert.cfrontend\
  -R CompCert/backend compcert.backend\
  -R CompCert/ia32 compcert.ia32\
  -R CompCert/common compcert.common\
  -R CompCert/lib compcert.lib\

##########################
#                        #
# Variables definitions. #
#                        #
##########################


OPT?=
COQDEP?="$(COQBIN)coqdep" -c
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQCHKFLAGS?=-silent -o
COQDOCFLAGS?=-interpolate -utf8
COQC?="$(COQBIN)coqc"
GALLINA?="$(COQBIN)gallina"
COQDOC?="$(COQBIN)coqdoc"
COQCHK?="$(COQBIN)coqchk"
COQEXEC="$(COQBIN)coqtop" $(COQLIBS) -batch -load-vernac-source

######################
#                    #
# Files dispatching. #
#                    #
######################

VFILES:=RMemory.v\
  DataflowToObc/Correctness.v\
  DataflowToObc/Correctness/MemoryCorres.v\
  DataflowToObc/Correctness/IsPresent.v\
  DataflowToObc/Translation.v\
  Obc.v\
  Obc/FuseIfte.v\
  Obc/Equiv.v\
  Obc/Semantics.v\
  Obc/Syntax.v\
  Dataflow.v\
  Dataflow/NoDup.v\
  Dataflow/Ordered.v\
  Dataflow/WellFormed/Decide.v\
  Dataflow/WellFormed.v\
  Dataflow/MemSemantics.v\
  Dataflow/Semantics.v\
  Dataflow/Clocking/Properties.v\
  Dataflow/Clocking/Parents.v\
  Dataflow/Clocking.v\
  Dataflow/Memories.v\
  Dataflow/IsDefined/Decide.v\
  Dataflow/IsDefined.v\
  Dataflow/IsVariable/Decide.v\
  Dataflow/IsVariable.v\
  Dataflow/IsFree/Decide.v\
  Dataflow/IsFree.v\
  Dataflow/Syntax.v\
  Dataflow/Stream.v\
  Common.v\
  Interface.v

-include $(addsuffix .d,$(VFILES))
.SECONDARY: $(addsuffix .d,$(VFILES))

VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
ifeq '$(HASNATDYNLINK)' 'true'
HASNATDYNLINK_OR_EMPTY := yes
else
HASNATDYNLINK_OR_EMPTY :=
endif

#######################################
#                                     #
# Definition of the toplevel targets. #
#                                     #
#######################################

all: $(VOFILES) 

spec: $(VIFILES)

gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

validate: $(VOFILES)
	$(COQCHK) $(COQCHKFLAGS) $(COQLIBS) $(notdir $(^:.vo=))

beautify: $(VFILES:=.beautified)
	for file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done
	@echo 'Do not do "make clean" until you are sure that everything went well!'
	@echo 'If there were a problem, execute "for file in $$(find . -name \*.v.old -print); do mv $${file} $${file%.old}; done" in your shell/'

.PHONY: all opt byte archclean clean install userinstall depend html validate extraction test extr compcert

compcert: CompCert/Makefile.config
	@cd CompCert; make -j 8 compcert.ini driver/Version.ml proof extraction

CompCert/Makefile.config:
	@cd CompCert; ./configure ia32-linux

test: compcert all extraction extr

extraction: extraction/STAMP

extraction/STAMP: $(VOFILES) extraction/Extraction.v
	@mkdir -p extraction/extract
	@rm -f extraction/extract/*.*
	@$(COQEXEC) extraction/Extraction.v
	@touch extraction/STAMP

extr:
	@find CompCert -name '*.cm*' -delete
	@ocamlbuild -use-ocamlfind -no-hygiene -j 8 -I CompCert/cparser -cflags $(MENHIR_INCLUDES),-w,-3,-w,-20 rustre.native
	@cp CompCert/compcert.ini _build/compcert.ini

####################
#                  #
# Special targets. #
#                  #
####################

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

clean:
	rm -f $(VOFILES) $(VIFILES) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml
	rm -f extraction/extract/*
	rm -f extraction/STAMP
	ocamlbuild -clean

archclean:
	rm -f *.cmx *.o

printenv:
	@"$(COQBIN)coqtop" -config
	@echo 'CAMLC =	$(CAMLC)'
	@echo 'CAMLOPTC =	$(CAMLOPTC)'
	@echo 'PP =	$(PP)'
	@echo 'COQFLAGS =	$(COQFLAGS)'
	@echo 'COQLIBINSTALL =	$(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL =	$(COQDOCINSTALL)'

# Makefile: _CoqProject
# 	mv -f $@ $@.bak
# 	"$(COQBIN)coq_makefile" -f $< -o $@


###################
#                 #
# Implicit rules. #
#                 #
###################

%.vo %.glob: %.v
	@echo "COQC $*.v"
	@$(COQC) $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

%.g.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS)  -html -g $< -o $@

%.v.d: %.v
	@echo "COQDEP $*.v"
	@$(COQDEP) -slash -exclude-dir extraction/CompCert $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.v.beautified:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

