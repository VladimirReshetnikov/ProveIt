#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
python verify.py
python verify_local.py
mkdir -p build
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > build/compile_stdout.txt 2>&1 || {
        cat build/compile_stdout.txt
        exit 1
    }
done
if grep -Eq 'Overfull|undefined references|multiply defined' build/article.log; then
    echo 'PDF build requires review; inspect build/article.log.' >&2
    exit 1
fi
cp build/article.pdf article.pdf
printf 'Built article.pdf and both exact verification receipts.\n'
