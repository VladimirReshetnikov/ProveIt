#!/usr/bin/env python3
"""Draft individual kY substitution transfers for Lean, without checking them."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
old_path = here.parent / 'nine-sharing-sign23-octic-delta-candidate/seed.json'
new_path = here.parent / 'nine-sharing-sign22-dodecic-ky-candidate/seed.json'
old_bytes, new_bytes = old_path.read_bytes(), new_path.read_bytes()
assert hashlib.sha256(old_bytes).hexdigest() == 'ee6079ea26dd120fab39789f83034947c18e0c8806945a1fc75fca62e1c65d41'
assert hashlib.sha256(new_bytes).hexdigest() == '3746dacafb661a8bab30caee81ec3b2130915a8b31adf8fe3630f6a541574f37'
old, new = json.loads(old_bytes), json.loads(new_bytes)
assert old['residuals'][2]['gate'] == 'kY'
old_rows, new_rows = old['residuals'], new['residuals']
assert len(old_rows) == 14 and len(new_rows) == 13
old_indices = [i for i in range(14) if i != 2]
ports = {'beta': 0, 'K0': 1, 'MC': 2, 'MF': 3}

def render(t):
    op = t[0]
    if op == 'num': return f'(Expr.constant ({t[1]} : ℤ))'
    if op == 'port': return f'(Expr.constant (p {ports[t[1]]}))'
    if op == 'var': return f'(Expr.var {t[1]})'
    assert op in ('add', 'sub', 'mul') and len(t) == 3
    symbol = {'add': '+', 'sub': '-', 'mul': '*'}[op]
    return f'({render(t[1])} {symbol} {render(t[2])})'

def module(start, end):
    lines = ['import DiophantineConsistency.Sign22Coordinate', '',
      '/-! SOURCE-ONLY: kY substitution transfers; no Lean compilation claimed. -/',
      'set_option autoImplicit false', 'noncomputable section',
      'namespace DiophantineConsistency.Sign22Transfers',
      'open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing',
      'open scoped LO.FirstOrder LO.FirstOrder.Arithmetic', 'open AdaptiveEquationSyntax2011',
      'variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]', '']
    for new_i in range(start, end):
        old_i = old_indices[new_i]
        old_row, new_row = old_rows[old_i], new_rows[new_i]
        name = old_row['gate']
        assert name == new_row['gate'] and name.isidentifier()
        lines += [f'def old{name} (p : Fin 4 → ℤ) : Expr (Fin 24) :=', '  ' + render(old_row['expr']), '',
                  f'def new{name} (p : Fin 4 → ℤ) : Expr (Fin 23) :=', '  ' + render(new_row['expr']), '']
        for side, ix, seed in [('old', old_i, 'SharingSeed23Octic'), ('new', new_i, 'SharingSeed22Dodecic')]:
            if ix == 0:
                claim = f'{seed}.firstResidual p = {side}{name} p'
            else:
                claim = f'(({seed}.remainingResiduals p).drop {ix-1}).head? = some ({side}{name} p)'
            lines += [f'theorem {side}_{name}_row (p : Fin 4 → ℤ) :', f'    {claim} := by rfl', '']
        lines += [f'theorem {name}_eval (p : Fin 4 → ℤ) (v : Fin 23 → V) :',
                  f'    (old{name} p).evalRing (fun j => ι (Sign22Coordinate.lift v j)) =',
                  f'      (new{name} p).evalRing (fun j => ι (v j)) := by',
                  f'  simp [old{name}, new{name}, Sign22Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,',
                  '    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]', '']
    lines += ['end DiophantineConsistency.Sign22Transfers']
    for i in range(start, end):
        lines.append(f'#print axioms DiophantineConsistency.Sign22Transfers.{new_rows[i]["gate"]}_eval')
    return '\n'.join(lines) + '\n'

for block in range(2):
    target = here / f'Sign22Transfers{block:02}.lean'
    if target.exists(): raise SystemExit(f'refusing to overwrite {target.name}')
    target.write_text(module(7*block, min(7*block+7, 13)))
print(json.dumps({'status': 'GENERATED_SOURCE_ONLY', 'transfers': 13,
                  'modules': 2, 'scope': 'uncompiled; no bridge claim'}, sort_keys=True))
