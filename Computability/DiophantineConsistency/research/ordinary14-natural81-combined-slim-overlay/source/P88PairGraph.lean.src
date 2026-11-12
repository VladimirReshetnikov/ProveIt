import DiophantineConsistency.Compact44.FreeJ13

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
  let J : Expr (Fin 13) := .var 0
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
  let g19 := a * c
  let b0 := X + g19
  let ell := E * kY
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  let folded_kBt := k * Bt
  let folded_g31 := g31 - folded_kBt
  let g32 := M * folded_g31
  let g33 := Y * qm
  let g34 := g32 + g33
  let folded_q3Bt := q3 * Bt
  let Z := g34 - folded_q3Bt
  let g38 := Z * Z
  let g39 := M * M
  let g40 := ell * g30
  let g41 := 1 + g40
  let g42 := g39 * g41
  let A0 := g38 - g42
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
  let rho := f2 - 1
  let Q := Delta * rho
  let I := c2 * i
  let g71 := I * I
  let g72 := g71 - Q
  let Fs := 1 + g72
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  let g78 := V + u
  let y2 := g78 * g78
  let g80 := g78 + V
  let g81 := u * g80
  let g82 := Q * g81
  let Fa := y2 - g82
  let A0sq := A0 * A0
  let A1sq := A1 * A1
  let pair := Fa * Fs
  let pairm := pair - 1
  let pair2 := pairm * pairm
  let sum01 := A0sq + A1sq
  let out := sum01 + pair2
  -- END LITERAL GRAPH
  ⟨A0, A1, Fa, Fs, out⟩

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
