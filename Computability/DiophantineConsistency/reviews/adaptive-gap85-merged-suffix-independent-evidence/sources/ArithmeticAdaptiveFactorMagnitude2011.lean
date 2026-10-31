import DiophantineConsistency.AdaptiveEquationSyntax2011
import DiophantineConsistency.ArithmeticSignedPairs

/-! Literal adaptive factors as internal signed pairs. No factor unit or
positivity is assumed. The negative-unit exclusions remain a separate step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact four factors in the literal 88-gate adaptive expression. -/
def factors (p : Fin 4 → ℤ) : Expr (Fin 13) × Expr (Fin 13) × Expr (Fin 13) × Expr (Fin 13) :=
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
  let g80 := V * V
  let g81 := y2 - g80
  let g82 := Q * g81
  let Fa := y2 - g82
  let F0 := 1 + A0
  let F1 := 1 + A1
  (F0,F1,Fa,Fs)

theorem expression_factors (p : Fin 4 → ℤ) :
    expressionAt p = (factors p).2.2.2 * ((factors p).2.2.1 *
      ((factors p).1 * (factors p).2.1)) - 1 := rfl

def pairEval {σ : Type*} (e : Expr σ) (v : σ → V) : Pair V :=
  (e.splitNatural.1.evalSemiring v,e.splitNatural.2.evalSemiring v)

private theorem pairEval_mul {σ : Type*} (e f : Expr σ) (v : σ → V) :
    pairEval (e*f) v = multiply (pairEval e v) (pairEval f v) := rfl

private theorem one_of_zero {σ : Type*} (e : Expr σ) (v : σ → V)
    (hz : InternalZero (e - 1) v) : Equivalent (pairEval e v) (natural (1:V)) := by
  apply equivalent_one.mpr
  change (Expr.sub e (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub e (Expr.constant 1)).splitNatural.2.evalSemiring v at hz
  simpa [Expr.splitNatural, NatExpr.evalSemiring, pairEval] using hz

/-- The literal adaptive zero forces all four signed magnitudes to one. -/
theorem expressionAt_factor_magnitudes (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt p) v) :
    magnitude (pairEval (factors p).1 v)=1 ∧
    magnitude (pairEval (factors p).2.1 v)=1 ∧
    magnitude (pairEval (factors p).2.2.1 v)=1 ∧
    magnitude (pairEval (factors p).2.2.2 v)=1 := by
  let a:=pairEval (factors p).1 v
  let b:=pairEval (factors p).2.1 v
  let c:=pairEval (factors p).2.2.1 v
  let d:=pairEval (factors p).2.2.2 v
  rw [expression_factors] at hz
  have h:=one_of_zero _ v hz
  rw [pairEval_mul,pairEval_mul,pairEval_mul] at h
  have hs : Equivalent (product5 a b c d (natural (1:V))) (natural (1:V)) := by
    have he : product5 a b c d (natural (1:V)) =
        multiply d (multiply c (multiply a b)) := by
      unfold product5
      rw [multiply_one]
      apply Prod.ext <;> simp only [multiply] <;> ring
    rw [he]
    exact h
  obtain ⟨ha,hb,hc,hd,_⟩ := product5_magnitudes hs
  exact ⟨ha,hb,hc,hd⟩

theorem current_factor_magnitudes (v : Fin 13 → V)
    (hz : InternalZero expression v) :
    magnitude (pairEval (factors CurrentWindowCarry2011.ports).1 v)=1 ∧
    magnitude (pairEval (factors CurrentWindowCarry2011.ports).2.1 v)=1 ∧
    magnitude (pairEval (factors CurrentWindowCarry2011.ports).2.2.1 v)=1 ∧
    magnitude (pairEval (factors CurrentWindowCarry2011.ports).2.2.2 v)=1 :=
  expressionAt_factor_magnitudes _ v hz

theorem current_natural_factor_magnitudes (v : Fin 13 → V)
    (hz : InternalZero naturalExpression v) :
    magnitude (pairEval (factors CurrentWindowCarry2011.ports).1 (fun j => v j+1))=1 ∧
    magnitude (pairEval (factors CurrentWindowCarry2011.ports).2.1 (fun j => v j+1))=1 ∧
    magnitude (pairEval (factors CurrentWindowCarry2011.ports).2.2.1 (fun j => v j+1))=1 ∧
    magnitude (pairEval (factors CurrentWindowCarry2011.ports).2.2.2 (fun j => v j+1))=1 :=
  current_factor_magnitudes _ ((internalZero_positiveShift expression v).mp hz)

end DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
