#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error ProveIt_Proof_Simplification_Review.tex
pdflatex -interaction=nonstopmode -halt-on-error ProveIt_Proof_Simplification_Review.tex
