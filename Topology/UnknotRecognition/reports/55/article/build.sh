#!/bin/sh
set -eu
cd "$(dirname "$0")"
# A checked-in bibliography keeps the build independent of BibTeX.
# references.bib is also supplied for integration into the repository article.
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
