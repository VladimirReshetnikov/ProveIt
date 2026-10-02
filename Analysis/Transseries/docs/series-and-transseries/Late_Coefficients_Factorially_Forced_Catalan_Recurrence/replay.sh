#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
MODE="${1:---full}"
if [[ "$MODE" != '--full' && "$MODE" != '--core-only' ]]; then
  printf 'Usage: bash replay.sh [--full|--core-only]\n' >&2
  exit 2
fi
python3 scripts/verify_manifest.py
OUT="$(mktemp -d "$PWD/replay-output.XXXXXX")"
printf 'Replay output: %s\n' "$OUT"
python3 scripts/verify.py --output-dir "$OUT"
python3 scripts/remainder_coefficients.py --output-dir "$OUT"
python3 scripts/remainder_checks.py --output-dir "$OUT"
if [[ "$MODE" == '--full' ]]; then
  python3 scripts/inverse_checks.py --output-dir "$OUT"
fi
python3 - "$OUT" "$MODE" <<'PY'
from pathlib import Path
import sys
out, mode = Path(sys.argv[1]), sys.argv[2]
files = ['exact_coefficients.csv', 'corrections.json', 'verification.json',
         'normalized_ratios.json', 'normalized_ratios.csv',
         'scalar-coefficients.json', 'remainder-checks.json']
if mode == '--full':
    files += ['inverse_checks.json', 'inverse_checks.csv',
              'original_inverse_checks.json', 'original_inverse_checks.csv',
              'numerical_tables.tex']
for name in files:
    if (out/name).read_bytes() != (Path('results')/name).read_bytes():
        raise SystemExit(f'Regenerated data differs: {name}')
print(f'All {len(files)} regenerated data files match exactly')
PY
if [[ "$MODE" == '--full' ]]; then
  cp late_factorial_coefficients.pdf "$OUT/original.pdf"
  bash build_pdf.sh
  python3 - "$OUT/original.pdf" <<'PY'
import hashlib,sys
from pathlib import Path
old=Path(sys.argv[1]).read_bytes()
new=Path('late_factorial_coefficients.pdf').read_bytes()
print('Rebuilt PDF SHA-256:',hashlib.sha256(new).hexdigest())
if old==new:
    print('Rebuilt PDF is byte-identical to the supplied PDF')
else:
    print('PDF bytes differ; TeX versions may change binary output. Inspect rendered output before replacing an archived PDF.')
PY
fi
printf 'Replay passed\n'
