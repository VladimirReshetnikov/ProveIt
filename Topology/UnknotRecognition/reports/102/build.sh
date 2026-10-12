#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error positive_cancellation.tex > build-pass1.log
pdflatex -interaction=nonstopmode -halt-on-error positive_cancellation.tex > build-pass2.log
printf 'Built article/positive_cancellation.pdf\n'
