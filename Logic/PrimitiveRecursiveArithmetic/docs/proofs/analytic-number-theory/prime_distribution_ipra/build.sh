#!/usr/bin/env bash
set -euo pipefail
package_dir="$(cd -- "$(dirname -- "$0")" && pwd)"
cd "$package_dir"
mkdir -p verification
python3 code/dirichlet_checks.py > verification/dirichlet_checks.json
python3 code/finite_sieve.py --self-check > verification/sieve_checks.json
python3 code/finite_swbv.py > verification/swbv_checks.json
python3 code/sharp_bt_certificates.py > verification/sharp_bt_checks.json
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf ../prime_distribution_ipra.pdf
