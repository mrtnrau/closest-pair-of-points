# - The -I flag introduces sub-directories
# - -use-ocamlfind is required to find packages (from Opam)
# - _tags file introduces packages, bin_annot flag for tool chain

.PHONY: all clean byte native profile debug sanity test

OCB_FLAGS = -use-ocamlfind -I src
OCB = ocamlbuild $(OCB_FLAGS)

all: native byte # profile debug

clean:
	$(OCB) -clean

native: sanity
	$(OCB) closest_pair.native

byte: sanity
	$(OCB) closest_pair.byte

profile: sanity
	$(OCB) -tag profile closest_pair.native

debug: sanity
	$(OCB) -tag debug closest_pair.byte

# check that packages can be found
sanity:
	ocamlfind query zarith

test: native
	./closest_pair.native 1 50000 60000 70000 80000 90000 100000