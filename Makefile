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

ocaml: extract
	ocamlfind ocamlopt -package str -c rack.mli rack.ml ocaml/rack_util.ml || \
	  ocamlopt -I +str -c rack.mli rack.ml ocaml/rack_util.ml
	ocamlfind ocamlopt -package str -linkpkg rack.ml ocaml/rack_util.ml test/test_rack.ml -o test_rack || \
	  ocamlopt -I +str str.cmxa rack.ml ocaml/rack_util.ml test/test_rack.ml -o test_rack
	ocamlfind ocamlopt -package str -linkpkg rack.ml ocaml/rack_util.ml ocaml/rack_cli.ml -o rack_cli || \
	  ocamlopt -I +str str.cmxa rack.ml ocaml/rack_util.ml ocaml/rack_cli.ml -o rack_cli
	ocamlfind ocamlopt -package str -linkpkg rack.ml ocaml/rack_util.ml test/test_rack_prop.ml -o test_rack_prop || \
	  ocamlopt -I +str str.cmxa rack.ml ocaml/rack_util.ml test/test_rack_prop.ml -o test_rack_prop
	ocamlfind ocamlopt -package str -linkpkg rack.ml ocaml/rack_util.ml test/test_rack_extended.ml -o test_rack_extended || \
	  ocamlopt -I +str str.cmxa rack.ml ocaml/rack_util.ml test/test_rack_extended.ml -o test_rack_extended
	ocamlfind ocamlopt -package str -linkpkg rack.ml ocaml/rack_util.ml ocaml/rack_bench.ml -o rack_bench || \
	  ocamlopt -I +str str.cmxa rack.ml ocaml/rack_util.ml ocaml/rack_bench.ml -o rack_bench

test: ocaml
	./test_rack
	./test_rack_prop
	./test_rack_extended

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

.PHONY: all extract doc ocaml test vos vok clean
