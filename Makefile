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
	  theories/Export.v theories/Example.v

ocaml: extract
	ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml test_rack.ml -o test_rack || \
	  ocamlopt -I +str str.cmxa rack.ml rack_util.ml test_rack.ml -o test_rack
	ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml rack_cli.ml -o rack_cli || \
	  ocamlopt -I +str str.cmxa rack.ml rack_util.ml rack_cli.ml -o rack_cli
	ocamlfind ocamlopt -package str -linkpkg rack.ml rack_util.ml test_rack_prop.ml -o test_rack_prop || \
	  ocamlopt -I +str str.cmxa rack.ml rack_util.ml test_rack_prop.ml -o test_rack_prop

test: ocaml
	./test_rack
	./test_rack_prop

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

vok: Makefile.coq
	$(MAKE) -f Makefile.coq vok

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -f rack.ml rack.mli *.cmi *.cmo *.cmx *.o
	rm -f rack_cli test_rack test_rack_prop
	rm -rf docs

.PHONY: all extract doc ocaml test vos vok clean
