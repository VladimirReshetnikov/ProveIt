#!/usr/bin/env bash
set -euo pipefail
package_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$package_dir"

if kpsewhich pdflatex.fmt >/dev/null 2>&1 && kpsewhich lmodern.sty >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error pnt_li_ipra.tex
  exit
fi

# Local fallback for an installed Debian TeX tree without generated indexes.
# It creates private runtime files and never modifies the system TeX tree.
pnt_tex_runtime=${PNT_TEX_RUNTIME:-$(mktemp -d "${TMPDIR:-/tmp}/pnt-li-ipra-tex.XXXXXX")}
mkdir -p -- "$pnt_tex_runtime"
export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf,/etc/texmf}'
export TEXFORMATS="$pnt_tex_runtime//:"
export TEXFONTMAPS="$pnt_tex_runtime//:"
if [[ ! -s "$pnt_tex_runtime/pdflatex.fmt" ]]; then
  (cd -- "$pnt_tex_runtime" && pdftex -ini -etex -jobname=pdflatex \
    -progname=pdflatex -interaction=nonstopmode -halt-on-error pdflatex.ini \
    > format-build.log 2>&1)
fi
cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cmextra.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/latxfont.map \
    > "$pnt_tex_runtime/pdftex.map"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error pnt_li_ipra.tex \
    > "$pnt_tex_runtime/pass${pass}.log" 2>&1
done
printf 'Compiled pnt_li_ipra.pdf\n'
