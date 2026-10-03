#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 asymptotic_coefficients.py --order 4
python3 root_coefficient_audit.py > root_coefficient_audit.json
python3 validate_asymptotics.py
python3 - <<'PY'
import json
import exact_recurrence as r
stored=json.load(open('exact_values.json'))
import sympy as s
audit=json.load(open('root_coefficient_audit.json'))
coeff=json.load(open('asymptotic_coefficients.json'))['coefficients']
assert s.simplify(s.sympify(audit['a1'])-s.sympify(coeff[1]['symbolic']))==0
assert s.simplify(s.sympify(audit['a2'])-s.sympify(coeff[2]['symbolic']))==0
ell,a=r.cumulant_recurrence(100)
assert [str(x) for x in a]==stored['a'][:101]
assert [str(x) for x in ell]==stored['ell'][:101]
assert r.insertion_recurrence(40)==a[:41]
assert r.brute_avoid(8)==a[:9]
print('Short replay passed: exact prefix, independent insertion rules, brute avoidance, and correction audit')
PY
