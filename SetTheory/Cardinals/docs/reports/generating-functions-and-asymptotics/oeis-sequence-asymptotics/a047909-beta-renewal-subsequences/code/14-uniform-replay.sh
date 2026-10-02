#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$PWD"
PYTHON="${PYTHON:-python3}"
case "${1:-}" in ""|--with-pdf) ;; *) printf 'Usage: bash replay.sh [--with-pdf]\n' >&2; exit 2;; esac
"$PYTHON" scripts/check_manifest.py
mkdir -p build/replay/scripts build/replay/logs
cp scripts/*.py build/replay/scripts/
for name in check_symbolic check_inverse check_uniform; do
  printf 'Running %s\n' "$name"
  "$PYTHON" "build/replay/scripts/$name.py" > "build/replay/logs/$name.txt"
done
"$PYTHON" scripts/validate_outputs.py "$ROOT/checks" "$ROOT/build/replay/scripts"
if [[ "${1:-}" == --with-pdf ]]; then
  OUTPUT_PDF="$ROOT/build/replayed-addendum.pdf" bash ./build.sh
fi
printf 'Replay passed. Fresh results and logs: %s/build/replay\n' "$ROOT"
