#!/usr/bin/env bash
set -euo pipefail

# Regenerate all exact symbolic tables, numerical data, and figures.
python -W error experiments.py --sample-size 300000 --max-dyadic-depth 120

# Compile the report. latexmk automatically performs the required reruns.
latexmk -pdf -interaction=nonstopmode -halt-on-error dyadic_stein_koopman_frontier.tex
