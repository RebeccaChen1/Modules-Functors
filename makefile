all: order orderedcoll pq tests

order: order.ml
	ocamlbuild order.byte

orderedcoll: orderedcoll.ml
	ocamlbuild orderedcoll.byte

o: order orderedcoll

pq: prioqueue.ml
	ocamlbuild prioqueue.byte

tests: tests.ml
	ocamlbuild tests.byte

clean: 
	rm -r _build
	rm *.byte
