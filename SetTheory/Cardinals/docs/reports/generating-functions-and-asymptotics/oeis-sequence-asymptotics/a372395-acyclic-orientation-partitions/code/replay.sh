#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python first_correction.py
python generic_second_correction.py
python validate_results.py
python - <<'PY'
import json
import mpmath as mp
mp.mp.dps=60
a=json.load(open('first_correction.json'))
b=json.load(open('generic_second_correction.json'))
for kind in ['unrestricted','distinct']:
    assert abs(mp.mpf(a[kind]['a1'])-mp.mpf(b[kind]['a1']))<mp.mpf('1e-45')
print('PASS: independently organized first corrections agree within 1e-45')
PY
