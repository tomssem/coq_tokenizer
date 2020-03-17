# Coq Tokenizer in Coq
A tokenizer for Coq written in Coq

## Dependencies
[Coq IO](http://coq.io/)

## Building
Run:
```
./make_makefile.sh
make
ocamlbuild main.native -use-ocamlfind -package io-system
```
