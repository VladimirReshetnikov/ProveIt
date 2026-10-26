#!/bin/sh
set -eu
packet_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$packet_dir"
xelatex -interaction=nonstopmode -halt-on-error report.tex
xelatex -interaction=nonstopmode -halt-on-error report.tex
