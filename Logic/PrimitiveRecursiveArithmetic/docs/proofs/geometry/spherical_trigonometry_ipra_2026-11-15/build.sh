#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 scripts/verify_identities.py
latexmk -pdf -interaction=nonstopmode -halt-on-error spherical_trigonometry_ipra.tex
