#!/usr/bin/env bash
# Full release replay: verify, recompute, compare, and rebuild the article.
set -euo pipefail
cd "$(dirname "$0")"
"${PYTHON:-python3}" code/verify_manifest.py
bash code/replay.sh "$@"
bash build_pdf.sh
