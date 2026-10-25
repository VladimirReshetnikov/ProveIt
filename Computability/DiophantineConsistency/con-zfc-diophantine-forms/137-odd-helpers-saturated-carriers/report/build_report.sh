#!/bin/sh
# Compile outside the sealed packet, with shell escape disabled.
set -eu
report_dir=$(CDPATH= cd "$(dirname "$0")" && pwd)
release_dir=$(CDPATH= cd "$report_dir/.." && pwd)
parent_dir=$(CDPATH= cd "$release_dir/.." && pwd)
output_dir="$parent_dir/$(basename "$release_dir")_tex_rebuild"
mkdir -p "$output_dir"
export SOURCE_DATE_EPOCH=1792886400
export FORCE_SOURCE_DATE=1
cache=$(mktemp -d "${TMPDIR:-/tmp}/conzfc-tex-XXXXXX")
trap 'rm -rf "$cache"' EXIT HUP INT TERM
export TEXMFVAR="$cache/var"
export TEXMFCONFIG="$cache/config"
mkdir -p "$TEXMFVAR" "$TEXMFCONFIG"
# Some minimal Debian containers have TeX files but no ls-R/configuration cache.
# Use the installed distribution directly, without installing or changing it.
if [ -z "$(kpsewhich latex.ltx)" ] && [ -f /usr/share/texlive/texmf-dist/tex/latex/base/latex.ltx ]; then
    export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
fi
if [ -z "$(kpsewhich pdflatex.fmt)" ]; then
    (cd "$cache" && pdftex -ini -interaction=nonstopmode -halt-on-error -no-shell-escape \
        -jobname=pdflatex -progname=pdflatex '*pdflatex.ini' > "$output_dir/format_build.log" 2>&1) || {
        cat "$output_dir/format_build.log" >&2; exit 1;
    }
    export TEXFORMATS="$cache:"
fi
cd "$report_dir"
for pass in 1 2; do
    pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape \
        -output-directory="$output_dir" report.tex > "$output_dir/pass_$pass.log" 2>&1 || {
        cat "$output_dir/pass_$pass.log" >&2; exit 1;
    }
done
printf '%s\n' "$output_dir/report.pdf"
