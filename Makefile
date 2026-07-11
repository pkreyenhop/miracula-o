.PHONY: all build clean test

all: build

build:
	dune build
	cp -f _build/default/bin/miracula.exe ./mira

clean:
	dune clean
	rm -f ./mira

test:
	dune runtest
