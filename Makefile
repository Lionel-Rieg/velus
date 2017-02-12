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

COQLIBS?=-R . Velus\
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

COQDOCLIBS?=-R . Velus\
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
COQDOCFLAGS?=-interpolate -utf8 -g
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
  NLustreToObc/Correctness.v\
  NLustreToObc/NLObcTyping.v\
  NLustreToObc/Correctness/MemoryCorres.v\
  NLustreToObc/Correctness/IsPresent.v\
  NLustreToObc/Translation.v\
  NLustreToObc/Fusible.v\
  Obc.v\
  Obc/Equiv.v\
  Obc/ObcSemantics.v\
  Obc/ObcSyntax.v\
  Obc/ObcTyping.v\
  Obc/Fusion.v\
  Lustre/Parser/LustreAst.v\
  Lustre/Parser/LustreParser.v\
  NLustre.v\
  NLustre/NoDup.v\
  NLustre/Ordered.v\
  NLustre/WellFormed.v\
  NLustre/MemSemantics.v\
  NLustre/NLSemantics.v\
  NLustre/NLClocking.v\
  NLustre/Memories.v\
  NLustre/IsDefined.v\
  NLustre/IsVariable.v\
  NLustre/IsFree.v\
  NLustre/NLSyntax.v\
  NLustre/NLTyping.v\
  NLustre/Stream.v\
  NLustre/NLSchedule.v\
  Common.v\
  Ident.v\
  Clocks.v\
  ObcToClight/ObcClightCommon.v\
  ObcToClight/Interface.v\
  ObcToClight/Generation.v\
  ObcToClight/Correctness.v\
  ObcToClight/MoreSeparation.v\
  ObcToClight/SepInvariant.v\
  ObcToClight/NLustreElab.v\
  VelusCorrectness.v\
  Operators.v\
  Instantiator.v\
  Traces.v\
  ClightToAsm.v

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

all: velus 

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

.PHONY: opt byte archclean clean install userinstall depend html validate compcert velus

compcert: CompCert/Makefile.config
	@cd CompCert; make -j 8 compcert.ini driver/Version.ml proof

CompCert/Makefile.config:
	@cd CompCert; ./configure ia32-linux

extraction/extract:
	@mkdir -p $@

extraction/STAMP: $(VOFILES) extraction/Extraction.v
	@mkdir -p extraction/extract
	@rm -f extraction/extract/*.*
	@$(COQEXEC) extraction/Extraction.v
	@touch extraction/STAMP

Lustre/Parser/LustreParser.v: Lustre/Parser/LustreParser.vy
	@$(MENHIR) --no-stdlib --coq $<

Lustre/Parser/LustreLexer.ml: Lustre/Parser/LustreLexer.mll
	ocamllex $<

extraction/extract/LustreLexer.ml: Lustre/Parser/LustreLexer.ml extraction/STAMP
	cp $< $@

extraction/extract/Relexer.ml: Lustre/Parser/Relexer.ml extraction/extract
	cp $< $@

Lustre/Parser/LustreParser2.mly: Lustre/Parser/LustreParser.vy
	$(MENHIR) --no-stdlib --coq --only-preprocess-u $< > $@

Lustre/Parser/LustreParser2.ml Lustre/Parser/LustreParser2.mli: \
		Lustre/Parser/LustreParser2.mly
	$(MENHIR) --no-stdlib --table $<

extraction/extract/LustreParser2.ml: Lustre/Parser/LustreParser2.ml \
		extraction/extract
	cp $< $@

extraction/extract/LustreParser2.mli: Lustre/Parser/LustreParser2.mli \
    		extraction/extract
	cp $< $@

extraction/extract/nlustrelib.ml: NLustre/nlustrelib.ml extraction/extract
	cp $< $@

extraction/extract/obclib.ml: Obc/obclib.ml extraction/extract
	cp $< $@

extraction/extract/interfacelib.ml: ObcToClight/interfacelib.ml \
    		extraction/extract
	cp $< $@

velus: compcert extraction/STAMP extraction/extract/LustreLexer.ml \
    	velusmain.ml extraction/extract/LustreParser2.mli \
	extraction/extract/LustreParser2.ml extraction/extract/Relexer.ml \
	veluslib.ml extraction/extract/interfacelib.ml \
	extraction/extract/nlustrelib.ml extraction/extract/obclib.ml
	@find CompCert -name '*.cm*' -delete
	@ocamlbuild -use-ocamlfind -no-hygiene -j 8 -I extraction/extract -cflags $(MENHIR_INCLUDES),-w,-3,-w,-20   -ignore Lexer velusmain.native
	@mv velusmain.native velus
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
	make -C Lustre/Parser clean

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
	@$(COQDEP) -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.v.beautified:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

