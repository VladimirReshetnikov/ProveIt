import DiophantineConsistency.Ordinary12FreeJ
import DiophantineConsistency.ArithmeticAdaptiveFactorThree2011
import DiophantineConsistency.ArithmeticAdaptiveMersenne2011

/-! Conditional historical model adapter. The names q, Y, X, t, R and J
are separate carrier data, not yet bound to the 95-row graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Ordinary12RankAdapter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveFactorThree2011
open DiophantineConsistency.ArithmeticAdaptiveMersenne2011
open DiophantineConsistency.Ordinary12FreeJ
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Two noncircular cancellation consequences, with all their hypotheses
explicit; neither is derived from the model factor split alone. -/
theorem conditional_compact44_cancellations (q Y X t R J : V)
    (hqpos : 0 < q) (hY : q^3 ∣ Y)
    (hH : q^5 ∣ (3+4*Y*(X+1))*t)
    (hq : q = (Exp.exp (590069:V)-1)*J+1)
    (h3 : q ∣ 3*Exp.exp R) : q^4 ∣ t ∧ q ∣ Exp.exp R := by
  constructor
  · exact cancel_factor_three q Y X t hqpos hY hH
  · exact cancel_three (590069:V) R q J (by norm_num) hq h3

/-- The factor-unit conclusion and cancellations together. The separate
carrier hypotheses are not consequences of `hzero` in this theorem. -/
theorem conditional_freeJ_split_and_cancellations
    (p : Fin 4 → ℤ) (v : Fin 12 → V) (hzero : InternalZero (literal p) v)
    (q Y X t R J : V) (hqpos : 0 < q) (hY : q^3 ∣ Y)
    (hH : q^5 ∣ (3+4*Y*(X+1))*t)
    (hq : q = (Exp.exp (590069:V)-1)*J+1)
    (h3 : q ∣ 3*Exp.exp R) :
    ((pairEval (core p).first v).1 = (pairEval (core p).first v).2 + 1 ∧
     (pairEval (core p).main v).1 = (pairEval (core p).main v).2 + 1 ∧
     (pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2 + 1) ∧
    q^4 ∣ t ∧ q ∣ Exp.exp R := by
  exact ⟨literal_factor_units p v hzero,
    conditional_compact44_cancellations q Y X t R J hqpos hY hH hq h3⟩
end DiophantineConsistency.Ordinary12RankAdapter
#print axioms DiophantineConsistency.Ordinary12RankAdapter.conditional_compact44_cancellations
#print axioms DiophantineConsistency.Ordinary12RankAdapter.conditional_freeJ_split_and_cancellations
