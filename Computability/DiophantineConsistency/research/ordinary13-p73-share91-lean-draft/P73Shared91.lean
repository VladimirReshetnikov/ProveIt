import DiophantineConsistency.Compact44.P73Graph

/-! Uncompiled source draft: this 91-operation graph replaces `(1+k*qm)*q3`
by `q3+k*(q3*qm)`. JSON comparison and provider ancestry remain external. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P73Shared91
open DiophantineConsistency AdaptiveEquationSyntax2011

set_option linter.unusedVariables false in
def graph91 (p : Fin 4 → ℤ) : P73Graph.Graph :=
  let j : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let f : Expr (Fin 13) := .var 3
  let i : Expr (Fin 13) := .var 4
  let T : Expr (Fin 13) := .var 5
  let X : Expr (Fin 13) := .var 6
  let Y : Expr (Fin 13) := .var 7
  let r : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let u : Expr (Fin 13) := .var 11
  let gamma : Expr (Fin 13) := .var 12
  let beta : Expr (Fin 13) := .constant (p 0)
  let K0 : Expr (Fin 13) := .constant (p 1)
  let MC : Expr (Fin 13) := .constant (p 2)
  let MF : Expr (Fin 13) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let g0 := 3 * j
  let J := 1 + g0
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := Y * q2
  let qF := q - F
  let C := qF - alpha
  let E := X * Y
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let c2 := c * c
  let a := E + Y
  let g15 := 4 * a
  let H := 3 + g15
  let g17 := a * a
  let Delta := H + g17
  let ac := a * c
  let b0 := X + ac
  let ell := E * kY
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  let g32 := M * g31
  let g33 := Y * qm
  let g34 := g32 + g33
  let g35 := q3 + k * M
  let g36 := Bt * g35
  let root0 := g34 - g36
  let g38 := ell * g30
  let rad0 := 1 + g38
  let g40 := root0 * root0
  let g41 := M * M
  let g42 := g41 * rad0
  let A0 := g40 - g42
  let g44 := qF * qm
  let G := alpha + g44
  let g46 := q2 - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let g52 := k - R
  let r0 := g52 - 1
  let g54 := U * gamma
  let g55 := E * q
  let g56 := g54 + g55
  let shift := g56 - r0
  let g58 := U * b0
  let g59 := H * shift
  let Dstar := g58 + g59
  let g61 := Dstar * Dstar
  let g62 := U * U
  let g63 := Delta * c2
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f2 := f * f
  let f2m := f2 - 1
  let Kaux := Delta * f2m
  let I := c2 * i
  let g71 := I * I
  let g72 := Delta * g71
  let As := f2m - g72
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  let g78 := V + u
  let y2 := g78 * g78
  let g80 := V * V
  let g81 := y2 - g80
  let g82 := Kaux * g81
  let g83 := y2 - g82
  let Aa := g83 - 1
  let g85 := A0 * A0
  let g86 := A1 * A1
  let g87 := g85 + g86
  let g88 := Aa * Aa
  let g89 := g87 + g88
  let g90 := As * As
  let g91 := g89 + g90
  -- END LITERAL GRAPH
  ⟨A0, A1, Aa, As, g91⟩

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
