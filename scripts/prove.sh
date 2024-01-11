#!/bin/bash
set -x

file=$1
rm -f proof proof.xfrat proof-comments
./cryptominisat5 "$file" proof-comments | tee cms.out | grep "^s"
grep -v "^c" proof-comments > proof
./frat-rs elab proof "$file" proof.xfrat
echo "frat-rs fin."
./cake_xlrup "$file" proof.xfrat
echo "cake fin."