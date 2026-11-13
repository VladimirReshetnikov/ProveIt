import DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011

/-! Literal 100-row ordinary12 graph and its raw/model factor identities.
The fixed port calibration and residual exclusions are not proved here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.Ordinary12Literal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011

structure Core where
  first : Expr (Fin 12)
  main : Expr (Fin 12)
  ordinary : Expr (Fin 12)
  output : Expr (Fin 12)

def core (p : Fin 4 → ℤ) : Core :=
  let j : Expr (Fin 12) := .var 0
  let F : Expr (Fin 12) := .var 1
  let alpha : Expr (Fin 12) := .var 2
  let t : Expr (Fin 12) := .var 3
  let T : Expr (Fin 12) := .var 4
  let X : Expr (Fin 12) := .var 5
  let Y : Expr (Fin 12) := .var 6
  let r : Expr (Fin 12) := .var 7
  let eta : Expr (Fin 12) := .var 8
  let zeta : Expr (Fin 12) := .var 9
  let n : Expr (Fin 12) := .var 10
  let gamma : Expr (Fin 12) := .var 11
  let beta : Expr (Fin 12) := .constant (p 0)
  let K0 : Expr (Fin 12) := .constant (p 1)
  let MC : Expr (Fin 12) := .constant (p 2)
  let MF : Expr (Fin 12) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let g0 := 6 * j
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
  let g19 := a * c
  let b0 := X + g19
  let ell := E * kY
  let g22 := k * qm
  let W := 1 + g22
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
  let g35 := W * q3
  let g36 := Bt * g35
  let Z := g34 - g36
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
  let f := 1 + t
  let f2 := f * f
  let rho := f2 - 1
  let Q := Delta * rho
  let oneQ := 1 - Q
  let den := c2 * c2
  let g73 := T * c
  let g74 := g73 - R
  let g75 := f2 * g74
  let V := g75 - c
  let vn := V + n
  let vn2 := vn * vn
  let g79 := V * V
  let g80 := vn2 - g79
  let g81 := Q * g80
  let g82 := vn2 - g81
  let h := g82 - 1
  let g84 := 2 * oneQ
  let bn := g84 * vn
  let g86 := den * h
  let g87 := Q * oneQ
  let AN := g86 + g87
  let g89 := AN * AN
  let g90 := Q * den
  let g91 := bn * bn
  let g92 := g90 * g91
  let N := g89 - g92
  let g94 := 1 + A0
  let g95 := 1 + A1
  let g96 := g94 * g95
  let g97 := 1 + N
  let g98 := g96 * g97
  let P12 := g98 - 1
  -- END LITERAL GRAPH
  ⟨g94, g95, g97, P12⟩

def literal (p : Fin 4 → ℤ) : Expr (Fin 12) := (core p).output

theorem literal_eq_factors (p : Fin 4 → ℤ) :
    literal p = (core p).first * (core p).main * (core p).ordinary - 1 := by
  rfl

/-- Raw integer evaluation is stated separately from model evaluation. -/
theorem raw_eval_eq_factors (p : Fin 4 → ℤ) (v : Fin 12 → ℤ) :
    (literal p).eval v = (core p).first.eval v * (core p).main.eval v *
      (core p).ordinary.eval v - 1 := by
  rw [literal_eq_factors]
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A literal internal zero gives product one for the three exact factor
pairs; no port, positivity or rank hypothesis is used. -/
theorem product_one_of_internal_zero (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (hz : InternalZero (literal p) v) :
    Equivalent (multiply (multiply (pairEval (core p).first v)
      (pairEval (core p).main v)) (pairEval (core p).ordinary v)) (natural (1:V)) := by
  rw [literal_eq_factors] at hz
  apply equivalent_one.mpr
  change (Expr.sub _ (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub _ (Expr.constant 1)).splitNatural.2.evalSemiring v at hz
  simpa [Expr.splitNatural, NatExpr.evalSemiring, pairEval, multiply] using hz

end DiophantineConsistency.Ordinary12Literal
#print axioms DiophantineConsistency.Ordinary12Literal.literal_eq_factors
#print axioms DiophantineConsistency.Ordinary12Literal.raw_eval_eq_factors
#print axioms DiophantineConsistency.Ordinary12Literal.product_one_of_internal_zero
