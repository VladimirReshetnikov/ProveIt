#!/usr/bin/env python3
"""Generate or verify literal Lean graph source only; never invoke Lean."""
import hashlib,json,sys
from pathlib import Path
H=Path(__file__).resolve().parent;D=H.parents[1]
raw=(D/'research/ordinary14-shifted-guard87-probe/candidate.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210'
g=json.loads(raw);assert len(g['source'])==87 and g['witnesses']==['J','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma','omega'] and g['fixed_numerals']==['beta','K0','MC','MF']
head='''import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Source-only proposal. No Lean elaboration or file binding is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P87ShiftedGuard
open DiophantineConsistency AdaptiveEquationSyntax2011

structure Graph where
  A0 : Expr (Fin 14)
  A1 : Expr (Fin 14)
  aux : Expr (Fin 14)
  gap : Expr (Fin 14)
  guardResidual : Expr (Fin 14)
  output : Expr (Fin 14)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
'''
lines=[f'  let {n} : Expr (Fin 14) := .var {i}' for i,n in enumerate(g['witnesses'])]+[f'  let {n} : Expr (Fin 14) := .constant (p {i})' for i,n in enumerate(g['fixed_numerals'])]+['  -- BEGIN LITERAL GRAPH']
for n,op,a,b in g['source']:
 assert op in ('+','-','*');lines.append(f'  let {n} := {a} {op} {b}')
lines+=['  -- END LITERAL GRAPH','  ⟨A0, A1, Fa, g72, guard, guarded_out⟩']
tail='''

theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =
    (((graph p).A0 * (graph p).A0 + (graph p).A1 * (graph p).A1) +
      (((graph p).aux - 1) * ((graph p).aux - 1) +
        (graph p).gap * (graph p).gap)) +
      ((graph p).guardResidual * (graph p).guardResidual) := by rfl

end P87ShiftedGuard

#print axioms P87ShiftedGuard.output_shape
'''
out=H/'P87ShiftedGuardGraph.lean'; rendered=(head+'\n'.join(lines)+tail).encode()
if sys.argv[1:]==['--check']:
 assert out.read_bytes()==rendered
elif not sys.argv[1:]:
 assert not out.exists(),'refusing to overwrite';out.write_bytes(rendered)
else:raise SystemExit('usage: make_graph.py [--check]')
print(json.dumps({'candidate_sha256':hashlib.sha256(raw).hexdigest(),'source_sha256':hashlib.sha256(rendered).hexdigest(),'operation_rows':87,'scope':'source generation only; no Lean elaboration'},sort_keys=True,indent=2))
