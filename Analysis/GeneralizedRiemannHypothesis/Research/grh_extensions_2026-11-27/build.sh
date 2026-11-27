#!/usr/bin/env bash
# Build the self-contained manuscript with TeX Live and BibTeX.
set -euo pipefail
cd "$(dirname "$0")"

if kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  bibtex report
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
else
  # Some minimal TeX Live images have the sources but no ls-R or format cache.
  # Build a task-local format; no system files are altered and no network is used.
  grh_tex_tree=/usr/share/texlive/texmf-dist
  if [[ ! -f "$grh_tex_tree/tex/latex/base/latex.ltx" ]]; then
    echo 'A configured TeX Live installation with pdfLaTeX and BibTeX is required.' >&2
    exit 1
  fi
  mkdir -p build-local
  grh_build_dir="$(pwd)/build-local"
  export TEXMF="{/usr/share/texmf,$grh_tex_tree}"
  (
    cd "$grh_build_dir"
    pdftex -ini -etex -jobname=pdflatex pdflatex.ini
  )
  export TEXFORMATS="$grh_build_dir"
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
      "$grh_tex_tree/fonts/map/dvips/amsfonts/cm.map" \
      "$grh_tex_tree/fonts/map/dvips/amsfonts/cmextra.map" \
      "$grh_tex_tree/fonts/map/dvips/amsfonts/symbols.map" \
      > "$grh_build_dir/pdftex.map"
  export TEXFONTMAPS="$grh_build_dir"
  pdftex -fmt=pdflatex -interaction=nonstopmode -halt-on-error report.tex
  bibtex report
  pdftex -fmt=pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdftex -fmt=pdflatex -interaction=nonstopmode -halt-on-error report.tex
fi
