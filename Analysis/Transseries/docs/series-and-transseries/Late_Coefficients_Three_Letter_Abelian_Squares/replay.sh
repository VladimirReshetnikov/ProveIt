#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if command -v sha256sum >/dev/null 2>&1; then
  sha256sum --check SHA256SUMS
else
  python3 - <<'PY'
import hashlib
from pathlib import Path
for line in Path('SHA256SUMS').read_text().splitlines():
    expected,name=line.split('  ',1)
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==expected,name
print('All package checksums verified')
PY
fi
work=$(mktemp -d "${TMPDIR:-/tmp}/honeycomb-replay.XXXXXXXX")
trap 'rm -rf "$work"' EXIT
cp verify.py verify_analytic.py "$work/"
python3 "$work/verify.py"
python3 "$work/verify_analytic.py"
cmp "$work/coefficients_0_500.txt" expected/coefficients_0_500.txt
printf '\nPASS: exact coefficient baseline matched; density, Stokes-integral, and Lambert-inverse sanity assertions passed; no network used.\n'
