#!/usr/bin/env python3
"""Generate an uncompiled Lean graph draft from the reviewed 88-gate JSON."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
src=ROOT/'research/ordinary13-ordinary-pair88-46/freej88.json'
raw=src.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='fc4627a15edc10f4cfcd3e6acf7df0896bb552a5f00cf238af6f1b5a349975bb'
g=json.loads(raw)
assert len(g['source'])==88 and g['witnesses']==['J','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']
assert g['fixed_numerals']==['beta','K0','MC','MF']
header='''import DiophantineConsistency.Compact44.FreeJ13

/-! Uncompiled 88-gate free-J graph. File binding and operation counting
remain external; the parent/unit transfer is a separate client. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P88Pair
open DiophantineConsistency AdaptiveEquationSyntax2011

structure Graph where
  A0 : Expr (Fin 13)
  A1 : Expr (Fin 13)
  aux : Expr (Fin 13)
  strong : Expr (Fin 13)
  output : Expr (Fin 13)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
'''
lines=[]
for i,name in enumerate(g['witnesses']): lines.append(f'  let {name} : Expr (Fin 13) := .var {i}')
for i,name in enumerate(g['fixed_numerals']): lines.append(f'  let {name} : Expr (Fin 13) := .constant (p {i})')
lines.append('  -- BEGIN LITERAL GRAPH')
for name,op,a,b in g['source']:
    assert op in ('+','-','*')
    lines.append(f'  let {name} := {a} {op} {b}')
lines.extend(['  -- END LITERAL GRAPH','  ⟨A0, A1, Fa, Fs, out⟩'])
tail='''

section Ring
variable {R : Type*} [CommRing R]

/-- Factored difference of squares, without expanding the carrier. -/
theorem gap_eval (v u : Expr (Fin 13)) (w : Fin 13 → R) :
    (u * ((v + u) + v)).evalRing w =
      (((v + u) * (v + u)) - v * v).evalRing w := by
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul]
  ring

theorem A0_eq (p : Fin 4 → ℤ) : (graph p).A0 = (FreeJ13.graph p).A0 := by rfl
theorem A1_eq (p : Fin 4 → ℤ) : (graph p).A1 = (FreeJ13.graph p).A1 := by rfl
theorem strong_eq (p : Fin 4 → ℤ) : (graph p).strong = (FreeJ13.graph p).strong := by rfl

theorem aux_eval_eq (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).aux.evalRing w = (FreeJ13.graph p).aux.evalRing w := by
  simp only [graph, FreeJ13.graph, gap_eval, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul]

theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).A0 * (graph p).A0 + (graph p).A1 * (graph p).A1 +
      ((graph p).aux * (graph p).strong - 1) * ((graph p).aux * (graph p).strong - 1) := by rfl

/-- Evaluation of the literal 88-gate output over an arbitrary commutative ring. -/
theorem output_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).output.evalRing w =
      let g := FreeJ13.graph p
      g.A0.evalRing w * g.A0.evalRing w + g.A1.evalRing w * g.A1.evalRing w +
        (g.aux.evalRing w * g.strong.evalRing w - 1) * (g.aux.evalRing w * g.strong.evalRing w - 1) := by
  rw [output_shape, A0_eq, A1_eq, strong_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_sub, Expr.evalRing_ofNat,
    Int.cast_one, Nat.cast_one, aux_eval_eq]

end Ring
end P88Pair

#print axioms P88Pair.gap_eval
#print axioms P88Pair.aux_eval_eq
#print axioms P88Pair.output_eval
'''
out=HERE/'P88PairGraph.lean'
if out.exists(): raise SystemExit('refusing to overwrite source')
out.write_text(header+'\n'.join(lines)+tail)
print('draft_sha256',hashlib.sha256(out.read_bytes()).hexdigest())
