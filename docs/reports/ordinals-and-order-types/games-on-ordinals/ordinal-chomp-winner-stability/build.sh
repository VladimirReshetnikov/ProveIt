#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 code/make_certificate.py
python3 code/verify_certificate.py
python3 code/test_certificate.py
python3 code/export_tables.py
pdflatex -interaction=nonstopmode -halt-on-error ordinal_chomp_counterexample.tex
pdflatex -interaction=nonstopmode -halt-on-error ordinal_chomp_counterexample.tex
pdflatex -interaction=nonstopmode -halt-on-error ordinal_chomp_counterexample.tex
