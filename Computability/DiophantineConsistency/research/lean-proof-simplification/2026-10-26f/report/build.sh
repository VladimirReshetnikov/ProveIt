#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mkdir -p .build

# Normal TeX Live installations need no environment overrides. The review
# environment had its TeX source tree but no filename database or formats;
# this fallback keeps all generated cache files in this directory.
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF="{$PWD/.build/texmf-var,$PWD/.build/texmf-config,/usr/share/texlive/texmf-dist,/usr/share/texmf,/etc/texmf}"
  export TEXMFVAR="$PWD/.build/texmf-var"
  export TEXMFCONFIG="$PWD/.build/texmf-config"
  export XDG_CACHE_HOME="$PWD/.build/font-cache"
  mkdir -p "$TEXMFVAR" "$TEXMFCONFIG" "$XDG_CACHE_HOME"
fi

fmt_args=()
if ! kpsewhich xelatex.fmt >/dev/null 2>&1; then
  if [[ ! -s .build/xelatex.fmt ]]; then
    (cd .build && xetex -ini -etex -jobname=xelatex \
      -interaction=nonstopmode -halt-on-error '\input xelatex.ini')
  fi
  fmt_args=(-fmt="$PWD/.build/xelatex.fmt")
fi
for pass in 1 2 3; do
  xelatex "${fmt_args[@]}" -interaction=nonstopmode -halt-on-error \
    -file-line-error proof_simplification_report.tex
done
printf '\nBuilt %s/proof_simplification_report.pdf\n' "$PWD"
