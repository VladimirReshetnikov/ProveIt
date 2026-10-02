#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ $# -gt 1 || ( $# -eq 1 && "$1" != "--extended" ) ]]; then
  echo "Usage: bash reproduce.sh [--extended]" >&2; exit 2
fi
python3 code/fixed/cyclic_covers.py
python3 - <<'PY'
from pathlib import Path
import json
root=Path('.')
assert json.loads((root/'code/fixed/cyclic-checks.json').read_text()) == json.loads((root/'data/expected-fixed-checks.json').read_text())
print('PASS: rational coefficients match frozen expected data')
PY
python3 code/models/check_models.py
python3 code/critical/check_symbolic.py
python3 code/critical/check_exact.py "$@"
python3 code/general/check_quartic.py
python3 code/general_coefficients.py
python3 code/check_additional_critical_grades.py
python3 code/check_degree_two_and_inverse.py
printf '\nPASS: all requested replay checks completed\n'
