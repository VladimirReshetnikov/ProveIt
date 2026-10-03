#!/bin/sh
# Identity-check first; TeX and all build caches run in a fresh external copy.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if test "$#" -ne 1; then echo 'Usage: sh build_report.sh EXTERNAL_EMPTY_OUTPUT_DIRECTORY' >&2; exit 2; fi
PYTHON=${PYTHON:-python3}
"$PYTHON" -I -B "$ROOT/verify_release.py" --verify-only
OUT=$1
"$PYTHON" -I -B -c 'from pathlib import Path; import sys; r=Path(sys.argv[1]).resolve(); p=Path(sys.argv[2]).resolve();
if p==r or r in p.parents: raise SystemExit("Output must be external to the release")
if p.exists() and (not p.is_dir() or any(p.iterdir())): raise SystemExit("Output must be absent or empty")
p.mkdir(parents=True,exist_ok=True)' "$ROOT" "$OUT"
OUT=$(CDPATH= cd -- "$OUT" && pwd)
BUILD=$(mktemp -d)
trap 'rm -rf "$BUILD"' EXIT HUP INT TERM
cp -pR "$ROOT" "$BUILD/source"
"$PYTHON" -I -B "$BUILD/source/verify_release.py" --verify-only
mkdir "$BUILD/tex-cache" "$BUILD/cache"
export TEXMFVAR="$BUILD/tex-cache" TEXMFCONFIG="$BUILD/tex-cache" TEXFORMATS="$BUILD/tex-cache:" XDG_CACHE_HOME="$BUILD/cache"
# Official TeX Live system locations are public installation paths.
if ! kpsewhich article.cls >/dev/null 2>&1; then export TEXMF="{/usr/share/texlive/texmf-dist,/usr/share/texmf}"; fi
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
 (cd "$BUILD/tex-cache" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=pdflatex -progname=pdflatex pdflatex.ini >format-build.log)
fi
if ! kpsewhich pdftex.map >/dev/null 2>&1; then
 : >"$BUILD/tex-cache/pdftex.map"
 for name in lm.map cm.map cmextra.map symbols.map latxfont.map; do
  MAP=$(kpsewhich "$name")
  if test -n "$MAP"; then cat "$MAP" >>"$BUILD/tex-cache/pdftex.map"; fi
 done
 export TEXFONTMAPS="$BUILD/tex-cache:"
fi
export TZ=UTC SOURCE_DATE_EPOCH=1790985600 FORCE_SOURCE_DATE=1 PYTHONDONTWRITEBYTECODE=1
cd "$BUILD/source"
for pass in 1 2 3; do
 pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error report32.tex >"$BUILD/pass-$pass.log" 2>&1 || { tail -80 "$BUILD/pass-$pass.log"; exit 1; }
done
if grep -E 'Overfull|undefined references|undefined citations' report32.log; then echo 'LaTeX layout/reference failure' >&2; exit 1; fi
cp report32.pdf report32.log "$OUT/"
printf '%s\n' 'PASS: article rebuilt in a fresh external copy; numerical replay is a separate command'
