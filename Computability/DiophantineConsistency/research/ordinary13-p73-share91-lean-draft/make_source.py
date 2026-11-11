#!/usr/bin/env python3
"""Generate the source-only 91-gate draft from the pinned P73 graph source."""
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
source = ROOT / 'Lean/DiophantineConsistency/Compact44/P73Graph.lean'
text = source.read_text()
start = text.index('def graph (p : Fin 4 → ℤ) : Graph :=')
end = text.index('\ntheorem output_eq', start)
block = text[start:end]
block = block.replace('def graph (p : Fin 4 → ℤ) : Graph :=',
                      'def graph91 (p : Fin 4 → ℤ) : P73Graph.Graph :=')
old = '  let g22 := k * qm\n  let W := 1 + g22\n  let M := q3 * qm\n'
assert block.count(old) == 1
block = block.replace(old, '  let M := q3 * qm\n')
old = '  let g35 := W * q3\n'
assert block.count(old) == 1
block = block.replace(old, '  let g35 := q3 + k * M\n')
header = '''import DiophantineConsistency.Compact44.P73Graph

/-! Uncompiled source draft: this 91-operation graph replaces `(1+k*qm)*q3`
by `q3+k*(q3*qm)`. JSON comparison and provider ancestry remain external. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P73Shared91
open DiophantineConsistency AdaptiveEquationSyntax2011

set_option linter.unusedVariables false in
'''
tail = '''
section Ring
variable {R : Type*} [CommRing R]

/-- Reassociation in an arbitrary commutative ring. -/
theorem share_eval (q k m : Expr (Fin 13)) (w : Fin 13 → R) :
    (q + k * (q * m)).evalRing w = ((1 + k * m) * q).evalRing w := by
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Nat.cast_one, Int.cast_one]
  ring

theorem A0_eval_eq (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph91 p).A0.evalRing w = (P73Graph.graph p).A0.evalRing w := by
  simp only [graph91, P73Graph.graph, share_eval, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul]

theorem A1_eq (p : Fin 4 → ℤ) : (graph91 p).A1 = (P73Graph.graph p).A1 := by rfl
theorem Aa_eq (p : Fin 4 → ℤ) : (graph91 p).Aa = (P73Graph.graph p).Aa := by rfl
theorem As_eq (p : Fin 4 → ℤ) : (graph91 p).As = (P73Graph.graph p).As := by rfl

theorem output_eq (p : Fin 4 → ℤ) : (graph91 p).output =
    (graph91 p).A0 * (graph91 p).A0 + (graph91 p).A1 * (graph91 p).A1 +
      (graph91 p).Aa * (graph91 p).Aa + (graph91 p).As * (graph91 p).As := by rfl

/-- Full evaluator equality for arbitrary integer ports and commutative rings. -/
theorem eval_eq (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph91 p).output.evalRing w = (P73Graph.graph p).output.evalRing w := by
  rw [output_eq, P73Graph.output_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_mul, A0_eval_eq, A1_eq, Aa_eq, As_eq]

end Ring
end P73Shared91

#print axioms P73Shared91.share_eval
#print axioms P73Shared91.A0_eval_eq
#print axioms P73Shared91.eval_eq
'''
out = HERE / 'P73Shared91.lean'
if out.exists():
    raise SystemExit('refusing to overwrite source')
out.write_text(header + block + tail)
print('original_graph_source_sha256', sha256(source.read_bytes()).hexdigest())
print('generated_source_sha256', sha256(out.read_bytes()).hexdigest())
