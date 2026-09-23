#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
for program in pdflatex python3; do
    command -v "$program" >/dev/null 2>&1 || {
        printf 'Required program not found: %s\n' "$program" >&2
        exit 1
    }
done
python3 verify.py
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape article.tex \
        > "build-pass-${pass}.log" 2>&1 || {
        tail -n 60 "build-pass-${pass}.log" >&2
        exit 1
    }
done
if grep -E 'undefined references|There were undefined|! LaTeX Error' article.log; then
    printf 'Unresolved LaTeX issue; inspect article.log.\n' >&2
    exit 1
fi
printf 'Built article.pdf; finite checks recorded in verification.json.\n'
