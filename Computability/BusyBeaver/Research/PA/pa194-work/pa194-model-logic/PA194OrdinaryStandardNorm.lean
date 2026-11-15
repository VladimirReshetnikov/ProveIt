import PA194OrdinaryStandardMap
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194OrdinaryNativeConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open LO.FirstOrder.Arithmetic.Bootstrapping
open DiophantineConsistency.StrictSigmaOneInduction
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
local instance : Structure language ℕ := natStructure

theorem ordinary_q_norm :
    (∀⁰ ∼bnd ordinaryRefutation).Evalb (M := ℕ) ![] ↔ ¬ordinaryRefutation.Evalb (M := ℕ) ![] := by
  have hb := DiophantineConsistency.StrictPiTwoBridge.eval_bnd_iff (M := ℕ) ordinaryRefutation_sigma
  have hnorm : (∀⁰ ∼bnd ordinaryRefutation).Evalb (M := ℕ) ![] ↔ ¬ordinaryRefutation.Evalb (M := ℕ) ![] := by
    rw [ConPA.ISigma1Transfer.evalb_all_neg]
    constructor
    · intro h hr
      obtain ⟨w,hw⟩ := hb.mp hr
      exact h w hw
    · intro h w hw
      exact h (hb.mpr ⟨w,hw⟩)
  exact hnorm
#print axioms ordinary_q_norm
end PA194OrdinaryNativeConsistency
