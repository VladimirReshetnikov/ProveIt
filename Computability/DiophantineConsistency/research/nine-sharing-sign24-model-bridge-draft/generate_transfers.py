#!/usr/bin/env python3
"""Draft individual q3 substitution transfers for Lean, without checking them."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
old_path = here.parent / 'nine-sharing-sign25-octic-ell-candidate/seed.json'
new_path = here.parent / 'nine-sharing-sign24-octic-q3-candidate/seed.json'
old_bytes, new_bytes = old_path.read_bytes(), new_path.read_bytes()
assert hashlib.sha256(old_bytes).hexdigest() == 'c95637ae24a57dba0ae1113a8256ed6f12d33f416f035f9cd4f92cffdbf59fc8'
assert hashlib.sha256(new_bytes).hexdigest() == '24a6dcf05b96112cfa332aafe4790a367c44b9a0cc033a74197f92d3520ab865'
old, new = json.loads(old_bytes), json.loads(new_bytes)
assert old['residuals'][0]['gate'] == 'q3'
old_rows, new_rows = old['residuals'][1:], new['residuals']
assert len(old_rows) == len(new_rows) == 15
ports = {'beta': 0, 'K0': 1, 'MC': 2, 'MF': 3}

def render(t):
    op = t[0]
    if op == 'num': return f'(Expr.constant ({t[1]} : ℤ))'
    if op == 'port': return f'(Expr.constant (p {ports[t[1]]}))'
    if op == 'var': return f'(Expr.var {t[1]})'
    assert op in ('add', 'sub', 'mul') and len(t) == 3
    symbol = {'add': '+', 'sub': '-', 'mul': '*'}[op]
    return f'({render(t[1])} {symbol} {render(t[2])})'

def module(block, start, end):
    lines = ['import DiophantineConsistency.Sign24Coordinate', '',
      '/-! SOURCE-ONLY: q3 substitution transfers; no Lean compilation claimed. -/',
      'set_option autoImplicit false', 'noncomputable section',
      'namespace DiophantineConsistency.Sign24Transfers',
      'open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing',
      'open scoped LO.FirstOrder LO.FirstOrder.Arithmetic', 'open AdaptiveEquationSyntax2011',
      'variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]', '']
    for i in range(start, end):
        old_row, new_row = old_rows[i], new_rows[i]
        name = old_row['gate']
        assert name == new_row['gate'] and name.isidentifier()
        lines += [f'def old{name} (p : Fin 4 → ℤ) : Expr (Fin 26) :=', '  ' + render(old_row['expr']), '',
                  f'def new{name} (p : Fin 4 → ℤ) : Expr (Fin 25) :=', '  ' + render(new_row['expr']), '',
                  f'theorem old_{name}_row (p : Fin 4 → ℤ) :',
                  f'    ((SharingSeed25Octic.remainingResiduals p).drop {i}).head? = some (old{name} p) := by rfl', '']
        if i == 0:
            lines += [f'theorem new_{name}_row (p : Fin 4 → ℤ) :',
                      f'    SharingSeed24Octic.firstResidual p = new{name} p := by rfl', '']
        else:
            lines += [f'theorem new_{name}_row (p : Fin 4 → ℤ) :',
                      f'    ((SharingSeed24Octic.remainingResiduals p).drop {i-1}).head? = some (new{name} p) := by rfl', '']
        lines += [f'theorem {name}_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)',
                  '    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :',
                  f'    (old{name} p).evalRing (fun j => ι (Sign24Coordinate.lift beta v j)) =',
                  f'      (new{name} p).evalRing (fun j => ι (v j)) := by',
                  f'  simp [old{name}, new{name}, Sign24Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,',
                  '    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, hp0]', '']
    lines += ['end DiophantineConsistency.Sign24Transfers']
    for i in range(start, end):
        lines.append(f'#print axioms DiophantineConsistency.Sign24Transfers.{old_rows[i]["gate"]}_eval')
    return '\n'.join(lines) + '\n'

for block in range(3):
    target = here / f'Sign24Transfers{block:02}.lean'
    if target.exists(): raise SystemExit(f'refusing to overwrite {target.name}')
    target.write_text(module(block, 5*block, 5*block+5))
print(json.dumps({'status': 'GENERATED_SOURCE_ONLY', 'transfers': 15,
                  'modules': 3, 'scope': 'uncompiled; no bridge claim'}, sort_keys=True))
