#!/bin/sh
# Run copied sources and compare deterministic receipts. No shipped file changes.
set -eu
cd "$(dirname "$0")"
ROOT=$(pwd)
PYTHON=${PYTHON:-python3}
mkdir -p .replay
TMP=$(mktemp -d "$ROOT/.replay/run-XXXXXX")
mkdir -p "$TMP/independent"
cp test_single_unit_acceleration.py "$TMP/"
cp independent/audit_accelerator.py "$TMP/independent/"
(cd "$TMP" && "$PYTHON" test_single_unit_acceleration.py >main.log)
(cd "$TMP" && "$PYTHON" independent/audit_accelerator.py >independent.log)
"$PYTHON" - "$ROOT" "$TMP" <<'PY'
import json,sys
from pathlib import Path
root,run=map(Path,sys.argv[1:])
for rel in ('test-results.json','independent/audit-results.json'):
    expected=json.loads((root/rel).read_text())
    actual=json.loads((run/rel).read_text())
    if expected!=actual:
        raise SystemExit('Receipt mismatch: '+rel)
    print('PASS: '+rel)
print('Both actual-CA replay receipts match exactly.')
PY
printf 'Replay directory: %s\n' "$TMP"
