#!/usr/bin/env sh
set -eu
packet_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT HUP INT TERM
cd "$packet_dir"
export SOURCE_DATE_EPOCH=1792540800
export FORCE_SOURCE_DATE=1
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build_dir" report.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build_dir" report.tex
cp "$build_dir/report.pdf" "$packet_dir/report.pdf"
