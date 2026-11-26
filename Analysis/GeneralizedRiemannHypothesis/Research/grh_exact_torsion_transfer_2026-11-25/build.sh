#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python3 checks/verify_exact_torsion.py
python3 checks/referee_exact_shell.py > checks/referee_exact_shell_results.json
python3 checks/compare_bounds.py
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
