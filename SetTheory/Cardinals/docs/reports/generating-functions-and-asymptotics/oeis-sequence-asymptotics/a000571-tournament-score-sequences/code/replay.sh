#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 scripts/run_checks.py
bash build_pdf.sh
printf 'Replay complete: assertions passed, results regenerated, report.pdf rebuilt.\n'
