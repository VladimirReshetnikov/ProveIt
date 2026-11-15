#!/usr/bin/env bash
# Build the article with a normal TeX installation; repair only private
# runtime state if a Debian TeX tree has no generated format/database.
set -euo pipefail
package_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$package_dir"

if kpsewhich pdflatex.fmt >/dev/null 2>&1 && kpsewhich lmodern.sty >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error jordan_ipra.tex
  exit
fi

# Minimal runtime fallback used in the delivery environment.  Ordinary users
# with an initialized TeX installation take the branch above.
tex_runtime=${JORDAN_TEX_RUNTIME:-$(mktemp -d "${TMPDIR:-/tmp}/jordan-ipra-tex.XXXXXX")}
mkdir -p -- "$tex_runtime"
export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf,/etc/texmf}'
export TEXFORMATS="$tex_runtime//:"
export TEXFONTMAPS="$tex_runtime//:"
if [[ ! -s "$tex_runtime/pdflatex.fmt" ]]; then
  (cd -- "$tex_runtime" && pdftex -ini -etex -jobname=pdflatex \
    -progname=pdflatex -interaction=nonstopmode -halt-on-error pdflatex.ini \
    > format-build.stdout.log 2>&1)
fi
cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cmextra.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/latxfont.map \
    > "$tex_runtime/pdftex.map"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error jordan_ipra.tex \
    > "$tex_runtime/article-pass${pass}.stdout.log" 2>&1
done
printf 'Built %s/jordan_ipra.pdf\nRuntime logs: %s\n' "$package_dir" "$tex_runtime"
