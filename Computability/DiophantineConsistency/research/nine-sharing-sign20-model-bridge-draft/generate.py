#!/usr/bin/env python3
"""Generate sign20 Lean syntax from the pinned external residual AST."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
source = here.parent / 'nine-sharing-sign20-degree20-e-candidate/seed.json'
raw = source.read_bytes()
assert hashlib.sha256(raw).hexdigest() == '2593aca2ac701ff9312fe5aff1719bbf4fd29a97e2c3e14642bf137d6ef8bf7d'
seed = json.loads(raw)
assert seed['witness_count'] == 20 and seed['total_coordinates'] == 21 and len(seed['residuals']) == 11
ports = {'beta': 0, 'K0': 1, 'MC': 2, 'MF': 3}
count = 0

def render(t, depth=0):
    global count
    count += 1
    assert count <= 100000 and depth <= 80 and isinstance(t, list) and t
    op = t[0]
    if op == 'num':
        assert len(t) == 2 and type(t[1]) is int and 0 <= t[1] <= 10
        return f'(Expr.constant ({t[1]} : ℤ))', 0
    if op == 'port':
        assert len(t) == 2 and t[1] in ports
        return f'(Expr.constant (p {ports[t[1]]}))', 0
    if op == 'var':
        assert len(t) == 2 and type(t[1]) is int and 1 <= t[1] <= 20
        return f'(Expr.var {t[1]})', 1
    assert len(t) == 3 and op in ('add', 'sub', 'mul')
    a, da = render(t[1], depth + 1)
    b, db = render(t[2], depth + 1)
    symbol = {'add': '+', 'sub': '-', 'mul': '*'}[op]
    return f'({a} {symbol} {b})', da + db if op == 'mul' else max(da, db)

terms = []
for row in seed['residuals']:
    term, degree = render(row['expr'])
    assert degree <= 10
    terms.append(term)
header = '''import DiophantineConsistency.NineFreshJones

/-! UNCOMPILED generated syntax. The external AST binding and all model
bridges require independent review and Lean checks. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed20Degree20

/-- First residual in the external candidate order. -/
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  ''' + terms[0] + '''

/-- Remaining 10 residuals in the external candidate order. -/
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 21)) :=
  [
'''
footer = '''
  ]

/-- Sum of the 11 squared residuals; coordinate 0 is unused. -/
def seed (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)

def zeroWitness (x : ℤ) (j : Fin 21) : ℤ := if j = 0 then x else 0
end DiophantineConsistency.SharingSeed20Degree20
'''
out = header + ',\n'.join('    ' + t for t in terms[1:]) + footer
target = here / 'SharingSeed20Degree20.lean'
if target.exists(): raise SystemExit('refusing to overwrite source')
target.write_text(out)
print(json.dumps({'status': 'GENERATED_SOURCE_ONLY', 'source_sha256': hashlib.sha256(out.encode()).hexdigest(),
                  'seed_json_sha256': hashlib.sha256(raw).hexdigest(), 'residuals': len(terms),
                  'ast_nodes': count, 'scope': 'no Lean check or model bridge'}, indent=2, sort_keys=True))
