import DiophantineConsistency.AdaptiveGap85ScaledNorms
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011

/-! Positive first and main Pell quotients from the actual 85 zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Quotients
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveQuotients2011
open AdaptiveGap85Literal AdaptiveGap85ScaledNorms
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first and main quotients are obtained rather than assumed. -/
theorem expressionAt_quotients85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let M : V := (q*(q*q))*(v 0*(p 0:V))
    let U : V := v 7*(q*q)
    let k : V := v 9+v 10
    let ell : V := (v 6*v 7)*(v 7*k)
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    let delta : V := (3+4*a)+a*a
    ∃ first main : V, 0<first ∧ 0<main ∧
      magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v) = M*first ∧
      first*first=1+ell*(ell+k) ∧
      magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).2.1) v) = U*main ∧
      main*main=1+delta*(c*c) := by
  have hp := scaled_parameters_positive p v hb hv
  have h := expressionAt_concrete_scaled_norms85 p v hz
  dsimp only at h ⊢
  obtain ⟨first,hfirst,hfn⟩ := scaled_quotient _ _ _ hp.2.1 h.1
  obtain ⟨main,hmain,hmn⟩ := scaled_quotient _ _ _ hp.2.2.1 h.2
  have hf : 0<first := pos_of_mul_pos_left (by rw [hfn]; simp) (by simp)
  have hg : 0<main := pos_of_mul_pos_left (by rw [hmn]; simp) (by simp)
  exact ⟨first,main,hf,hg,hfirst,hfn,hmain,hmn⟩
end DiophantineConsistency.AdaptiveGap85Quotients
