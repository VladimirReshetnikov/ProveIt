import DiophantineConsistency.AdaptiveGap85Units
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011

/-! Scaled Pell norms of the actual 85 factors, retaining signed roots. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ScaledNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 AdaptiveGap85Literal AdaptiveGap85Units
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem first_shape85 (p : Fin 4 → ℤ) :
    (AdaptiveGap85Factors.factors p).1 = 1 + (rootTerm (AdaptiveGap85Factors.factors p).1 * rootTerm (AdaptiveGap85Factors.factors p).1 - rightTerm (AdaptiveGap85Factors.factors p).1) := rfl
private theorem main_shape85 (p : Fin 4 → ℤ) :
    (AdaptiveGap85Factors.factors p).2.1 = 1 + (rootTerm (AdaptiveGap85Factors.factors p).2.1 * rootTerm (AdaptiveGap85Factors.factors p).2.1 - rightTerm (AdaptiveGap85Factors.factors p).2.1) := rfl

/-- The actual first and main signed roots satisfy their scaled norm equations. -/
theorem expressionAt_scaled_norms85 (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt85 p) v) :
    magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors p).1) v)*magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors p).1) v) +
        (pairEval (rightTerm (AdaptiveGap85Factors.factors p).1) v).2 = (pairEval (rightTerm (AdaptiveGap85Factors.factors p).1) v).1 ∧
    magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors p).2.1) v)*magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors p).2.1) v) +
        (pairEval (rightTerm (AdaptiveGap85Factors.factors p).2.1) v).2 = (pairEval (rightTerm (AdaptiveGap85Factors.factors p).2.1) v).1 := by
  obtain ⟨h0,h1,_,_⟩ := expressionAt_factor_units85 p v hz
  rw [first_shape85 p] at h0
  rw [main_shape85 p] at h1
  exact ⟨unit_square_norm _ _ _ h0,unit_square_norm _ _ _ h1⟩

/-- The right sides are positive-syntax expressions for natural ports. -/
theorem expressionAt_concrete_scaled_norms85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let M : V := (q*(q*q))*(v 0*(p 0:V))
    let U : V := v 7*(q*q)
    let k : V := v 9+v 10
    let ell : V := (v 6*v 7)*(v 7*k)
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    let delta : V := (3+4*a)+a*a
    magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v)*
      magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v) = M*M*(1+ell*(ell+k)) ∧
    magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).2.1) v)*
      magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).2.1) v) = U*U*(1+delta*(c*c)) := by
  have h := expressionAt_scaled_norms85 (fun j => (p j:ℤ)) v hz
  have h0 : pairEval (rightTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v =
      pairEval (rightTerm (ArithmeticAdaptiveFactorMagnitude2011.factors (fun j => (p j:ℤ))).1) v := rfl
  have h1 : pairEval (rightTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).2.1) v =
      pairEval (rightTerm (ArithmeticAdaptiveFactorMagnitude2011.factors (fun j => (p j:ℤ))).2.1) v := rfl
  rw [h0,h1,first_rhs_pair p v,main_rhs_pair p v] at h
  simpa only [Prod.fst,Prod.snd,add_zero] using h
end DiophantineConsistency.AdaptiveGap85ScaledNorms
