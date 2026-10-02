#!/bin/sh
# Fast consistency and receipt validation without modifying this package.
set -eu
cd "$(dirname "$0")"
root=$(pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
cp check*.py *verification.json hamiltonian-rank.tex "$work/"
cp -R alphabet exact "$work/"
cd "$work"
export PYTHONDONTWRITEBYTECODE=1
python3 check_general.py > general-new.json
diff -u general-verification.json general-new.json
python3 check_lower.py > lower-new.json
diff -u lower-verification.json lower-new.json
python3 check.py > restricted-new.json
diff -u verification.json restricted-new.json
python3 check_templates.py > templates-new.json
python3 alphabet/check_fixed_alphabet_lemmas.py > fixed-new.json
python3 alphabet/check_ternary_bookkeeping.py > multicolor-new.json
python3 exact/validate_receipts.py
python3 exact/four_state/audit_families.py > families-new.json
python3 exact/four_state/check_literal_four.py
python3 exact/four_state/validate_receipts.py
if [ "${1:-}" = "--compile" ]; then
  g++ -O3 -std=c++17 exact/audit_census.cpp -o census
  ./census 2 > two-new.json
  g++ -O3 -std=c++17 -Wno-return-type exact/compare_pointwise.cpp -o compare
  ./compare 2 > pointwise-new.json
  g++ -O3 -std=c++17 exact/four_state/four_state_prune_budget.cpp -o candidates
  ./candidates > candidates-budget.txt 2> candidates.txt
  python3 - <<'PY'
import pathlib,json,hashlib
r=pathlib.Path('.')
assert json.loads((r/'two-new.json').read_text())==json.loads((r/'exact/independent_two_state.json').read_text())
assert json.loads((r/'pointwise-new.json').read_text())['pointwise_three_algorithm_comparisons']==2304
receipt=json.loads((r/'exact/four_state/audit_receipt.json').read_text())
data=(r/'candidates.txt').read_bytes()
assert len(data.splitlines())==23228
assert hashlib.sha256(data).hexdigest()==receipt['candidate_list_sha256']
print('Independent two-state census, three-way pointwise check, and four-state candidate generation passed')
PY
fi
printf 'All selected verification checks passed\n'
