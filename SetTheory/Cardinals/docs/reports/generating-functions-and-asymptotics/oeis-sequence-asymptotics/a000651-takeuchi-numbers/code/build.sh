#!/bin/sh
# Build with a complete TeX distribution, or bootstrap its missing local caches.
# This script installs nothing and writes only within the package directory.
set -eu
cd "$(dirname "$0")"
mkdir -p receipts .build
if ! command -v pdflatex >/dev/null 2>&1 || ! command -v kpsewhich >/dev/null 2>&1; then
    printf '%s\n' 'pdfLaTeX and kpsewhich are required; install a TeX distribution.' >&2
    exit 1
fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1 || ! kpsewhich pdftex.map >/dev/null 2>&1; then
    # Minimal read-only TeX images sometimes contain source packages but omit
    # the generated filename databases, format, and font maps. Permit normal
    # directory search and place regenerated assets in this writable folder.
    TEXMF=$(kpsewhich -var-value=TEXMF | sed 's/!!//g')
    TEXMFVAR="$PWD/.build/texmf-var"
    TEXMFCONFIG="$PWD/.build/texmf-config"
    TEXMFCACHE="$PWD/.build/texmf-cache"
    export TEXMF TEXMFVAR TEXMFCONFIG TEXMFCACHE
    if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
        (cd .build && pdftex -ini -interaction=nonstopmode -halt-on-error \
            -jobname=pdflatex -progname=pdflatex '*pdflatex.ini' \
            > ../receipts/latex-format-rebuild.txt)
        TEXFORMATS="$PWD/.build:"
        export TEXFORMATS
    fi
    if ! kpsewhich pdftex.map >/dev/null 2>&1; then
        : > .build/pdftex.map
        for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
            map=$(kpsewhich "$name") || { printf 'Missing font map %s\n' "$name" >&2; exit 1; }
            cat "$map" >> .build/pdftex.map
        done
        TEXFONTMAPS="$PWD/.build:"
        export TEXFONTMAPS
    fi
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error takeuchi-asymptotics.tex > "receipts/latex-rebuild-$pass.txt"
done
printf '%s\n' 'Built takeuchi-asymptotics.pdf'
