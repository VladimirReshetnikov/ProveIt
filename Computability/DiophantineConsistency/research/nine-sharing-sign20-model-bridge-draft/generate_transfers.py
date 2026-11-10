#!/usr/bin/env python3
"""Draft individual E substitution transfers for Lean, without checking them."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
old_path = here.parent / 'nine-sharing-sign21-degree14-s-candidate/seed.json'
new_path = here.parent / 'nine-sharing-sign20-degree20-e-candidate/seed.json'
old_bytes, new_bytes = old_path.read_bytes(), new_path.read_bytes()
assert hashlib.sha256(old_bytes).hexdigest() == '85ad59859a6ebc62f8a4de250ac7abf3af904601e8f6c9e696351d5247ea6e81'
assert hashlib.sha256(new_bytes).hexdigest() == '2593aca2ac701ff9312fe5aff1719bbf4fd29a97e2c3e14642bf137d6ef8bf7d'
old, new = json.loads(old_bytes), json.loads(new_bytes)
assert old['residuals'][1]['gate'] == 'E'
old_rows, new_rows = old['residuals'], new['residuals']
assert len(old_rows) == 12 and len(new_rows) == 11
old_indices = [i for i in range(12) if i != 1]
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
    lines = ['import DiophantineConsistency.Sign20Coordinate', '',
      '/-! SOURCE-ONLY: E substitution transfers; no Lean compilation claimed. -/',
      'set_option autoImplicit false', 'noncomputable section',
      'namespace DiophantineConsistency.Sign20Transfers',
      'open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing',
      'open scoped LO.FirstOrder LO.FirstOrder.Arithmetic', 'open AdaptiveEquationSyntax2011',
      'variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]', '']
    for new_i in range(start, end):
        old_i = old_indices[new_i]
        old_row, new_row = old_rows[old_i], new_rows[new_i]
        name = old_row['gate']
        assert name == new_row['gate'] and name.isidentifier()
        lines += [f'def old{name} (p : Fin 4 → ℤ) : Expr (Fin 22) :=', '  ' + render(old_row['expr']), '',
                  f'def new{name} (p : Fin 4 → ℤ) : Expr (Fin 21) :=', '  ' + render(new_row['expr']), '']
        for side, ix, seed in [('old', old_i, 'SharingSeed20Degree20'), ('new', new_i, 'SharingSeed20Degree20')]:
            if ix == 0:
                claim = f'{seed}.firstResidual p = {side}{name} p'
            else:
                claim = f'(({seed}.remainingResiduals p).drop {ix-1}).head? = some ({side}{name} p)'
            lines += [f'theorem {side}_{name}_row (p : Fin 4 → ℤ) :', f'    {claim} := by rfl', '']
        lines += [f'theorem {name}_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)',
                  '    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :',
                  f'    (old{name} p).evalRing (fun j => ι (Sign20Coordinate.lift beta v j)) =',
                  f'      (new{name} p).evalRing (fun j => ι (v j)) := by',
                  f'  simp [old{name}, new{name}, Sign20Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,',
                  '    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat, hp0]', '']
    lines += ['end DiophantineConsistency.Sign20Transfers']
    for i in range(start, end):
        lines.append(f'#print axioms DiophantineConsistency.Sign20Transfers.{new_rows[i]["gate"]}_eval')
    return '\n'.join(lines) + '\n'

for block in range(2):
    target = here / f'Sign20Transfers{block:02}.lean'
    if target.exists(): raise SystemExit(f'refusing to overwrite {target.name}')
    target.write_text(module(6*block, min(6*block+6, 11)))
print(json.dumps({'status': 'GENERATED_SOURCE_ONLY', 'transfers': 11,
                  'modules': 2, 'scope': 'uncompiled; no bridge claim'}, sort_keys=True))
