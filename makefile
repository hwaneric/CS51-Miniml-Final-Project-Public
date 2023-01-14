all: miniml expr evaluation tests

miniml: miniml.ml 
	ocamlbuild -use-ocamlfind miniml.byte	

expr: expr.ml
	ocamlbuild -use-ocamlfind expr.byte

evaluation: evaluation.ml
	ocamlbuild -use-ocamlfind evaluation.byte

tests: tests.ml
	ocamlbuild -use-ocamlfind tests.byte

clean:
	rm -rf _build *.byte