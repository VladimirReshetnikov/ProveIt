#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
mkdir -p .build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex > .build/pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex > .build/pass2.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.build article.tex > .build/pass3.txt
cp .build/article.pdf ../Cycle_Block_Kernels.pdf
cp .build/article.log ../results/article_build.log
