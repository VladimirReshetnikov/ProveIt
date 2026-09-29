#!/usr/bin/env sh
# ed. (2026-09-29): the delivered script reran both programs in place, rewriting
# the recorded results/ and figures/ (the figure bytes are not reproducible), and
# left its pass logs beside the article. It now writes fresh verification output to
# build/results/, a fresh figure to build/figures/, and the LaTeX pass logs and
# auxiliary files to build/; the article is typeset from the recorded figure and
# only article.pdf is replaced. Compare build/ with the recorded files to check a
# rerun. Set PYTHON to choose the interpreter (default: python).
set -eu
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python}"
mkdir -p build
"$PYTHON" verify.py --out build/results
(cd build && "$PYTHON" ../make_figure.py)
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > "build/build-pass-${pass}.log"
done
cp build/article.pdf article.pdf
printf 'Built article.pdf; fresh verification results in build/results/, fresh figure in build/figures/\n'
