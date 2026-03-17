COQMAKEFILE := rocq makefile -f _CoqProject

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -o Makefile.coq

extract: all
	@echo "Extraction complete: rack.ml, rack.mli"

doc: all
	mkdir -p docs
	coqdoc --html --interpolate --utf8 \
	  -R theories RACK \
	  -d docs \
	  theories/Core.v theories/Main.v theories/Reflect.v \
	  theories/Export.v theories/Notation.v \
	  theories/EvidenceClass.v theories/ProofIdentity.v \
	  theories/Entailment.v theories/Trace.v \
	  theories/Delta.v theories/Incremental.v \
	  theories/ProductLine.v theories/Bridge.v \
	  theories/CaseStudy.v theories/Example.v

OCAMLOPT := ocamlfind ocamlopt -package str -I ocaml -I test

ocaml: extract
	$(OCAMLOPT) -c rack.mli rack.ml ocaml/rack_util.ml
	$(OCAMLOPT) -c test/test_rack.ml
	$(OCAMLOPT) -c test/test_rack_prop.ml
	$(OCAMLOPT) -c test/test_rack_extended.ml
	$(OCAMLOPT) -c ocaml/rack_cli.ml
	$(OCAMLOPT) -c ocaml/rack_bench.ml
	$(OCAMLOPT) -linkpkg rack.cmx ocaml/rack_util.cmx test/test_rack.cmx -o test_rack
	$(OCAMLOPT) -linkpkg rack.cmx ocaml/rack_util.cmx test/test_rack_prop.cmx -o test_rack_prop
	$(OCAMLOPT) -linkpkg rack.cmx ocaml/rack_util.cmx test/test_rack_extended.cmx -o test_rack_extended
	$(OCAMLOPT) -linkpkg rack.cmx ocaml/rack_util.cmx ocaml/rack_cli.cmx -o rack_cli
	$(OCAMLOPT) -linkpkg rack.cmx ocaml/rack_util.cmx ocaml/rack_bench.cmx -o rack_bench

test: ocaml
	./test_rack
	./test_rack_prop
	./test_rack_extended

DEEPSPEC_FLAGS := -R theories RACK -w -notation-overridden,-redundant-canonical-projection,-future-coercion-class-field,-deprecated-from-Coq -native-compiler no

deepspec: all
	rocq compile $(DEEPSPEC_FLAGS) theories/VSTBridge.v
	rocq compile $(DEEPSPEC_FLAGS) theories/ITreeBridge.v
	rocq compile $(DEEPSPEC_FLAGS) -R deepspec max deepspec/max.v
	rocq compile $(DEEPSPEC_FLAGS) -R deepspec max deepspec/verif_max.v
	rocq compile $(DEEPSPEC_FLAGS) -R deepspec max deepspec/DeepSpecVST.v
	rocq compile $(DEEPSPEC_FLAGS) -R deepspec max deepspec/DeepSpecITree.v
	rocq compile $(DEEPSPEC_FLAGS) -R deepspec max deepspec/ConopsITree.v

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

vok: Makefile.coq
	$(MAKE) -f Makefile.coq vok

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -f rack.ml rack.mli *.cmi *.cmo *.cmx *.o
	rm -f rack_cli rack_bench test_rack test_rack_prop test_rack_extended
	rm -f ocaml/*.cmi ocaml/*.cmo ocaml/*.cmx ocaml/*.o
	rm -f test/*.cmi test/*.cmo test/*.cmx test/*.o
	rm -rf docs

.PHONY: all extract doc ocaml test deepspec vos vok clean
