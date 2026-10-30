import DiophantineConsistency.AdaptiveGap85Factors
import DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011

/-! An actual 85 zero forces all four signed factor magnitudes to one. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Magnitudes
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveGap85Literal AdaptiveGap85Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem pairEval_mul85 (e f : Expr (Fin 13)) (v : Fin 13 → V) :
    pairEval (e*f) v=multiply (pairEval e v) (pairEval f v) := rfl
private theorem one_of_zero85 (e : Expr (Fin 13)) (v : Fin 13 → V)
    (hz : InternalZero (e-1) v) : Equivalent (pairEval e v) (natural (1:V)) := by
  apply equivalent_one.mpr
  change (Expr.sub e (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub e (Expr.constant 1)).splitNatural.2.evalSemiring v at hz
  simpa [Expr.splitNatural,NatExpr.evalSemiring,pairEval] using hz

/-- No unit signs are assumed: all four actual signed magnitudes are one. -/
theorem expressionAt_factor_magnitudes85 (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt85 p) v) :
    magnitude (pairEval (AdaptiveGap85Factors.factors p).1 v)=1 ∧
    magnitude (pairEval (AdaptiveGap85Factors.factors p).2.1 v)=1 ∧
    magnitude (pairEval (AdaptiveGap85Factors.factors p).2.2.1 v)=1 ∧
    magnitude (pairEval (AdaptiveGap85Factors.factors p).2.2.2 v)=1 := by
  let a:=pairEval (AdaptiveGap85Factors.factors p).1 v
  let b:=pairEval (AdaptiveGap85Factors.factors p).2.1 v
  let c:=pairEval (AdaptiveGap85Factors.factors p).2.2.1 v
  let d:=pairEval (AdaptiveGap85Factors.factors p).2.2.2 v
  rw [AdaptiveGap85Factors.expression_factors] at hz
  have h:=one_of_zero85 _ v hz
  rw [pairEval_mul85,pairEval_mul85,pairEval_mul85] at h
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
end DiophantineConsistency.AdaptiveGap85Magnitudes
