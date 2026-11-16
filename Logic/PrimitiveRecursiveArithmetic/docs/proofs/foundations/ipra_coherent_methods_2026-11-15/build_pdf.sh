#!/usr/bin/env bash
set -euo pipefail
project_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
cd "$project_dir/paper"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  tex_runtime_dir=${TEX_WORK_DIR:-"$project_dir/.tex-runtime"}
  mkdir -p "$tex_runtime_dir"
  export TEXMF='{/usr/share/texlive/texmf-dist,/usr/share/texmf,/etc/texmf}'
  export TEXFORMATS="$tex_runtime_dir//:"
  export TEXFONTMAPS="$tex_runtime_dir//:"
  if [[ ! -f "$tex_runtime_dir/pdflatex.fmt" ]]; then
    (
      cd "$tex_runtime_dir"
      pdftex -ini -etex -jobname=pdflatex -progname=pdflatex \
        -interaction=nonstopmode -halt-on-error pdflatex.ini >format.log 2>&1
    )
  fi
  if [[ ! -f "$tex_runtime_dir/pdftex.map" ]]; then
    cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cmextra.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map \
      /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/latxfont.map \
      > "$tex_runtime_dir/pdftex.map"
  fi
fi
for pass in 1 2 3; do
  if ! pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error \
      ipra_coherent_methods.tex > "../validation/latex_pass_$pass.txt" 2>&1; then
    tail -60 "../validation/latex_pass_$pass.txt"
    exit 1
  fi
done
if rg -n 'Undefined control sequence|LaTeX Warning: (Reference|Citation).*undefined|There were undefined references|multiply defined' ipra_coherent_methods.log; then
  exit 1
fi
printf '%s\n' 'Compiled ipra_coherent_methods.pdf successfully.'
pdfinfo ipra_coherent_methods.pdf > ../validation/pdfinfo.txt
