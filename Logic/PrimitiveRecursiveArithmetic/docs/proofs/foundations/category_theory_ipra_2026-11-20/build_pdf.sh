#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
if command -v pdflatex >/dev/null 2>&1; then
  task_tex_build=$(mktemp -d)
  trap 'rm -rf -- "$task_tex_build"' EXIT
  # Some minimal distributions contain packages but omit generated databases,
  # formats and font maps. Bootstrap those locally without changing the host.
  if ! kpsewhich -progname=pdflatex -format=fmt pdflatex.fmt >/dev/null 2>&1; then
    if ! kpsewhich -progname=pdflatex pdflatex.ini >/dev/null 2>&1; then
      if [[ -d /usr/share/texlive/texmf-dist ]]; then
        export TEXMF='{/etc/texmf,/usr/share/texmf,/usr/share/texlive/texmf-dist}'
      fi
    fi
    task_tex_ini=$(kpsewhich -progname=pdflatex pdflatex.ini)
    (
      cd -- "$task_tex_build"
      pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
        -jobname=pdflatex -progname=pdflatex "$task_tex_ini" > format-build.log
    )
    export TEXFORMATS="$task_tex_build:${TEXFORMATS:-}"
  fi
  if ! kpsewhich -format=map pdftex.map >/dev/null 2>&1; then
    for task_tex_map in lm.map cm.map cmextra.map symbols.map latxfont.map; do
      cat -- "$(kpsewhich -format=map "$task_tex_map")" >> "$task_tex_build/pdftex.map"
    done
    export TEXFONTMAPS="$task_tex_build:${TEXFONTMAPS:-}"
  fi
  for task_tex_pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error category_theory_ipra.tex
  done
elif command -v tectonic >/dev/null 2>&1; then
  tectonic -X compile category_theory_ipra.tex --keep-logs
else
  echo 'Install Tectonic or a complete pdfLaTeX distribution to build the report.' >&2
  exit 1
fi
