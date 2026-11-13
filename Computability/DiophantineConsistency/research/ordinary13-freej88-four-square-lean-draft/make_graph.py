#!/usr/bin/env python3
"""Produce source-only graph draft from the external candidate; never run Lean."""
import hashlib, json
from pathlib import Path
here = Path(__file__).resolve().parent
project = here.parents[1]
raw = (project / 'research/ordinary13-four-square88-30/candidate.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'
g = json.loads(raw)
assert len(g['source']) == 88
assert g['witnesses'] == ['J','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']
assert g['fixed_numerals'] == ['beta','K0','MC','MF']
head = '''import P88PairGraph

/-! Source-only draft; graph/file binding and operation count are external. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P88FourSquare
open DiophantineConsistency AdaptiveEquationSyntax2011

structure Graph where
  A0 : Expr (Fin 13)
  A1 : Expr (Fin 13)
  aux : Expr (Fin 13)
  gap : Expr (Fin 13)
  output : Expr (Fin 13)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
'''
lines = [f'  let {name} : Expr (Fin 13) := .var {i}' for i,name in enumerate(g['witnesses'])]
lines += [f'  let {name} : Expr (Fin 13) := .constant (p {i})' for i,name in enumerate(g['fixed_numerals'])]
lines.append('  -- BEGIN LITERAL GRAPH')
for name, op, a, b in g['source']:
    assert op in ('+', '-', '*')
    lines.append(f'  let {name} := {a} {op} {b}')
lines += ['  -- END LITERAL GRAPH', '  ⟨A0, A1, Fa, g72, out⟩']
tail = '''

section Ring
variable {R : Type*} [CommRing R]

theorem A0_eq (p : Fin 4 → ℤ) : (graph p).A0 = (P88Pair.graph p).A0 := by rfl
theorem A1_eq (p : Fin 4 → ℤ) : (graph p).A1 = (P88Pair.graph p).A1 := by rfl
theorem aux_eq (p : Fin 4 → ℤ) : (graph p).aux = (P88Pair.graph p).aux := by rfl
theorem strong_shape (p : Fin 4 → ℤ) :
    (P88Pair.graph p).strong = 1 + (graph p).gap := by rfl

theorem gap_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).gap.evalRing w = (P88Pair.graph p).strong.evalRing w - 1 := by
  rw [strong_shape]
  simp only [Expr.evalRing_add, Expr.evalRing_ofNat, Nat.cast_one]
  ring

theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =
    ((graph p).A0 * (graph p).A0 + (graph p).A1 * (graph p).A1) +
      (((graph p).aux - 1) * ((graph p).aux - 1) +
        (graph p).gap * (graph p).gap) := by rfl

/-- Arbitrary-ring evaluation, retaining the pair parent's residuals. -/
theorem output_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).output.evalRing w =
      let g := P88Pair.graph p
      (g.A0.evalRing w * g.A0.evalRing w + g.A1.evalRing w * g.A1.evalRing w) +
        ((g.aux.evalRing w - 1) * (g.aux.evalRing w - 1) +
          (g.strong.evalRing w - 1) * (g.strong.evalRing w - 1)) := by
  rw [output_shape, A0_eq, A1_eq, aux_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_sub,
    Expr.evalRing_ofNat, Nat.cast_one, gap_eval]

end Ring
end P88FourSquare

#print axioms P88FourSquare.strong_shape
#print axioms P88FourSquare.gap_eval
#print axioms P88FourSquare.output_eval
'''
out = here / 'P88FourSquareGraph.lean'
assert not out.exists(), 'refusing to overwrite'
out.write_text(head + '\n'.join(lines) + tail)
print(json.dumps({'candidate_sha256': hashlib.sha256(raw).hexdigest(), 'source_sha256': hashlib.sha256(out.read_bytes()).hexdigest()}))
