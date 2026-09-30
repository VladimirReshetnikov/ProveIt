#!/usr/bin/env sh
# ed. (2026-09-29): the delivered script reran verify.py in place before
# typesetting, rewriting all six recorded results/ files (including the table
# the article inputs, and the Python version string), and wrote its pass logs and
# TeX auxiliary files beside the article. It now writes fresh verification output
# to build/results/ and the pass logs and auxiliary files to build/; the article is
# typeset from the recorded results/coalescence_table.tex and only article.pdf is
# replaced. Compare build/results/ with results/ to check a rerun. Set PYTHON to
# choose the interpreter (default: python).
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
PYTHON="${PYTHON:-python}"
mkdir -p build
"$PYTHON" verify.py --stage all --outdir build/results
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > "build/build_pass_${pass}.txt"
done
cp build/article.pdf article.pdf
printf '%s\n' 'Built article.pdf; fresh results in build/results/. See build/article.log for TeX diagnostics.'
