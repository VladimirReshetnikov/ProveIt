#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$PWD"
PYTHON="${PYTHON:-python3}"
sha256sum -c SHA256SUMS
mkdir -p build/replay
cd build/replay
"$PYTHON" "$ROOT/scripts/derive_coefficients.py" --order 8 > coefficient-output.txt
"$PYTHON" "$ROOT/scripts/verify_counts.py" > count-output.txt
"$PYTHON" "$ROOT/scripts/verify_law_inversion.py" > law-inversion-output.txt
"$PYTHON" "$ROOT/scripts/verify_sectors.py" > sector-output.txt
"$PYTHON" "$ROOT/scripts/compare_results.py" "$ROOT/data" "$PWD"
cd "$ROOT"
OUTPUT_PDF="$ROOT/build/replayed-report.pdf" bash ./build.sh
printf '\nReplay passed. Fresh results: %s/build/replay\nFresh PDF: %s/build/replayed-report.pdf\n' "$ROOT" "$ROOT"
