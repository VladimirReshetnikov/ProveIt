#!/usr/bin/env bash
set -euo pipefail
packet_dir="$(cd -- "$(dirname -- "$0")/.." && pwd)"
cd -- "$packet_dir"
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
