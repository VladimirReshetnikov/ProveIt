#!/usr/bin/env sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT HUP INT TERM
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
fi
export TEXMFVAR="$build_dir" TEXMFCONFIG="$build_dir" TEXFORMATS="$build_dir:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd "$build_dir" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini >format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
  : >"$build_dir/pdftex.map"
  for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
    cat "$(kpsewhich "$name")" >>"$build_dir/pdftex.map"
  done
  export TEXFONTMAPS="$build_dir:"
fi
export TZ=UTC
export SOURCE_DATE_EPOCH=1790985600
export FORCE_SOURCE_DATE=1
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build_dir" fixed-input-timed-quartics.tex > "$build_dir/pass1.log" 2>&1 || { tail -80 "$build_dir/pass1.log"; exit 1; }
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build_dir" fixed-input-timed-quartics.tex > "$build_dir/pass2.log" 2>&1 || { tail -80 "$build_dir/pass2.log"; exit 1; }
if grep -E 'Overfull|undefined references|undefined citations' "$build_dir/fixed-input-timed-quartics.log"; then
  echo 'LaTeX layout or reference warning' >&2
  exit 1
fi
cp "$build_dir/fixed-input-timed-quartics.pdf" fixed-input-timed-quartics.pdf
printf '%s\n' 'PDF build PASS'
