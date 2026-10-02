#!/bin/sh
set -eu
cd "$(dirname "$0")"
build_dir="$(mktemp -d)"
trap 'rm -rf "$build_dir"' EXIT HUP INT TERM
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build_dir" hamiltonian-rank.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build_dir" hamiltonian-rank.tex
cp "$build_dir/hamiltonian-rank.pdf" hamiltonian-rank.pdf
