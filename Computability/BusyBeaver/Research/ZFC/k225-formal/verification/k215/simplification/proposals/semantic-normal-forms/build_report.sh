#!/bin/sh
set -eu
REPORT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPORT_BUILD=$(mktemp -d)
trap 'rm -rf "$REPORT_BUILD"' EXIT HUP INT TERM
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$REPORT_BUILD" "$REPORT_DIR/report.tex"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$REPORT_BUILD" "$REPORT_DIR/report.tex"
cp "$REPORT_BUILD/report.pdf" "$REPORT_DIR/report.pdf"
