"""Optional independent direct-phase eigenvalue replay."""
from pathlib import Path
import json,sys
import sympy as s
from matrix_math import direct_pressure
ROOT=Path(__file__).resolve().parents[1]
reference=json.loads((ROOT/'data/direct_phase_reference.json').read_text())['rows']
for m in map(int,sys.argv[1:] or range(2,6)):
 row=next(x for x in reference if x['m']==m)
 p=direct_pressure(m,6*m-2)
 for v in row['coefficients_after_missing']:
  if v['degree']<=6*m-2:assert p[v['degree']]==s.Rational(v['coefficient'])
 print('Direct phase recurrence passes at m=',m,flush=True)
