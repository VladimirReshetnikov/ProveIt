#!/bin/sh
set -eu
cd "$(dirname "$0")"
export SOURCE_DATE_EPOCH=1792800000
# Normally use the installed distribution. The fallback supports the
# provided minimal TeX environment without writing to the home directory.
if [ -z "$(kpsewhich article.cls 2>/dev/null || true)" ]; then
export TEXINPUTS='.:/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:'
export TEXFORMATS="$PWD/texcache//:"
export TEXMFVAR="$PWD/texcache/var"
export TEXMFCONFIG="$PWD/texcache/config"
export TEXFONTMAPS='/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:'
export TFMFONTS='/usr/share/texmf/fonts/tfm//:/usr/share/texlive/texmf-dist/fonts/tfm//:'
export T1FONTS='/usr/share/texmf/fonts/type1//:/usr/share/texlive/texmf-dist/fonts/type1//:'
export VFFONTS='/usr/share/texmf/fonts/vf//:/usr/share/texlive/texmf-dist/fonts/vf//:'
export ENCFONTS='/usr/share/texmf/fonts/enc//:/usr/share/texlive/texmf-dist/fonts/enc//:'
mkdir -p texcache
cat /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cmextra.map /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/latxfont.map /usr/share/texmf/fonts/map/dvips/lm/lm.map > texcache/pdftex.map
export TEXFONTMAPS="$PWD/texcache:$TEXFONTMAPS"
if [ ! -f texcache/pdflatex.fmt ]; then (cd texcache; pdftex -ini -etex -jobname=pdflatex -progname=pdflatex pdflatex.ini > format.log); fi
fi
for p in 1 2 3; do
 pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape report.tex > "build-$p.log"
done
printf 'Built report/report.pdf\n'
