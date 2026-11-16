#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 scripts/check_identities.py
latexmk -pdf -interaction=nonstopmode -halt-on-error von_mangoldt_totient_ipra.tex
