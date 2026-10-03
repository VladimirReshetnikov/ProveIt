#!/bin/sh
set -eu
cd "$(dirname "$0")/article"
pdflatex -interaction=nonstopmode -halt-on-error fixed-power-partition-asymptotics.tex
pdflatex -interaction=nonstopmode -halt-on-error fixed-power-partition-asymptotics.tex
