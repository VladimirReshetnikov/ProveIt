#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
PYTHON="${PYTHON:-python3}"
OUT="$(mktemp -d "${TMPDIR:-/tmp}/historic-tree-replay.XXXXXXXX")"
# Leave the temporary output available for review, including logs on failure.
printf 'Isolated replay directory: %s\n' "$OUT"
exec "$PYTHON" "$ROOT/code/run_replay.py" --output-dir "$OUT"
