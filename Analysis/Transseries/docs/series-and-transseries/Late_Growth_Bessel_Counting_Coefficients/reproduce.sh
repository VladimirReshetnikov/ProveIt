#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
PYTHON=${PYTHON:-python3}
case "${1:-}" in
  ""|--with-pdf) ;;
  *) echo 'Usage: bash reproduce.sh [--with-pdf]' >&2; exit 2 ;;
esac
"$PYTHON" scripts/verify_manifest.py
"$PYTHON" scripts/replay.py
"$PYTHON" scripts/verify_manifest.py --results-only
if [[ "${1:-}" == --with-pdf ]]; then
  bash build_pdf.sh
  "$PYTHON" scripts/verify_manifest.py --pdf-only
fi
printf 'PASS: complete reproducibility replay\n'
