#!/bin/sh
# Copy all sources to a fresh external workspace before compiling or regenerating.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if test "$#" -lt 1 || test "$#" -gt 2; then echo 'Usage: ./build.sh /external/empty/output [--regenerate-figures]' >&2; exit 2; fi
REGEN=0
if test "$#" -eq 2; then test "$2" = '--regenerate-figures' || exit 2; REGEN=1; fi
python3 -I -B "$ROOT/replay.py" --verify-only
OUT=$1
python3 -I -B -c 'from pathlib import Path; import sys; r=Path(sys.argv[1]).resolve(); p=Path(sys.argv[2]).resolve();
if p==r or r in p.parents: raise SystemExit("Output must be external")
if p.exists() and (not p.is_dir() or any(p.iterdir())): raise SystemExit("Output must be absent or empty")
p.mkdir(parents=True,exist_ok=True)' "$ROOT" "$OUT"
OUT=$(CDPATH= cd -- "$OUT" && pwd)
BUILD=$(mktemp -d)
trap 'rm -rf "$BUILD"' EXIT HUP INT TERM
cp -pR "$ROOT" "$BUILD/source"
mkdir "$BUILD/tex-cache" "$BUILD/cache"
export TEXMFVAR="$BUILD/tex-cache" TEXMFCONFIG="$BUILD/tex-cache" TEXFORMATS="$BUILD/tex-cache:" MPLCONFIGDIR="$BUILD/cache" XDG_CACHE_HOME="$BUILD/cache"
if ! kpsewhich article.cls >/dev/null 2>&1; then export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"; fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
 (cd "$BUILD/tex-cache" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini >format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
 : >"$BUILD/tex-cache/pdftex.map"
 for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do cat "$(kpsewhich "$name")" >>"$BUILD/tex-cache/pdftex.map"; done
 export TEXFONTMAPS="$BUILD/tex-cache:"
fi
export TZ=UTC SOURCE_DATE_EPOCH=1790985600 FORCE_SOURCE_DATE=1 PYTHONDONTWRITEBYTECODE=1
if test "$REGEN" -eq 1; then
 python3 -I -B "$BUILD/source/figures/make_figures.py" --output-dir "$BUILD/generated-figures" >"$BUILD/figures.log"
 cp "$BUILD/generated-figures/"*.pdf "$BUILD/source/figures/"
 cp "$BUILD/generated-figures/simulation-data.json" "$OUT/"
 cp "$BUILD/figures.log" "$OUT/"
fi
cd "$BUILD/source"
for pass in 1 2 3; do
 pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error report31.tex >"$BUILD/pass-$pass.log" 2>&1 || { tail -80 "$BUILD/pass-$pass.log"; exit 1; }
done
if grep -E 'Overfull|undefined references|undefined citations' report31.log; then echo 'LaTeX layout/reference failure' >&2; exit 1; fi
cp report31.pdf report31.log "$OUT/"
printf '%s\n' 'PASS: PDF rebuilt in a fresh external copy'
