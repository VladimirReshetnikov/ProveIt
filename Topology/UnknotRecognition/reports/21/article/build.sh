#!/bin/sh
set -eu
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error certified_disk_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error certified_disk_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error certified_disk_frontiers.tex
