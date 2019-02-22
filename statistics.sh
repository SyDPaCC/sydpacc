#! /bin/sh

echo === Coq ===
coqwc $(find . -name "*.v")

echo === OCaml ===
wc -l $(find Uncertified -name "*.ml";find Uncertified -name "*.mli")

echo === C ===
wc -l $(find Uncertified -name "*.c") $(find Uncertified -name "*.h")
