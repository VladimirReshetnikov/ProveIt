#!/bin/sh
set -eu
artifact_source_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
artifact_build_dir=$(mktemp -d "$artifact_source_dir/.report-build.XXXXXX")
trap 'rm -rf "$artifact_build_dir"' 0 HUP INT TERM
cd "$artifact_source_dir"
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -file-line-error -output-directory "$artifact_build_dir" report.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -file-line-error -output-directory "$artifact_build_dir" report.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -file-line-error -output-directory "$artifact_build_dir" report.tex
cp "$artifact_build_dir/report.pdf" "$artifact_source_dir/report.pdf"
