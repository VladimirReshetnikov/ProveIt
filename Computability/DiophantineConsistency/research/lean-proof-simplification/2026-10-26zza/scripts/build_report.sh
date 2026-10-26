#!/usr/bin/env bash
set -euo pipefail
packet_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$packet_dir"
xelatex -interaction=nonstopmode -halt-on-error report.tex
xelatex -interaction=nonstopmode -halt-on-error report.tex
