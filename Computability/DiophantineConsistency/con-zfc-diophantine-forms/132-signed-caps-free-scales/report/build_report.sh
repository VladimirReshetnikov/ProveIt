#!/bin/sh
# Rebuild outside the sealed packet: no delivered source or PDF is overwritten.
set -eu
report_dir=$(CDPATH= cd "$(dirname "$0")" && pwd)
release_dir=$(CDPATH= cd "$report_dir/.." && pwd)
parent_dir=$(CDPATH= cd "$release_dir/.." && pwd)
output_dir="$parent_dir/$(basename "$release_dir")_tex_rebuild"
mkdir -p "$output_dir"
cd "$report_dir"
export SOURCE_DATE_EPOCH=1792886400
export FORCE_SOURCE_DATE=1
cache=$(mktemp -d "${TMPDIR:-/tmp}/conzfc-tex-XXXXXX")
trap 'rm -rf "$cache"' EXIT HUP INT TERM
export TEXMFVAR="$cache/var"
export TEXMFCONFIG="$cache/config"
mkdir -p "$TEXMFVAR" "$TEXMFCONFIG"
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape -output-directory="$output_dir" report.tex >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape -output-directory="$output_dir" report.tex >/dev/null
printf '%s\n' "$output_dir/report.pdf"
