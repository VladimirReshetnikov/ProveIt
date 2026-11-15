import PA194OrdinaryStandardRefutation
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

theorem ordinary_q_standard (q : Semisentence language 1)
    (hq : PRA ⊢ (Semiformula.lMap embedding (∀⁰ ∼bnd ordinaryRefutation) 🡘 ∀⁰ q)) :
    (∀⁰ q).Evalb (M := ℕ) ![] ↔ Entailment.Consistent PA194PAeq.ordinaryPAeq := by
  have hmap := ordinary_q_map q hq
  rw [ordinary_q_norm,ordinary_refutation_standard] at hmap
  have hs : ¬Provable PA194PAeq.ordinaryPAeq (⌜(⊥ : Sentence PA194PAeq.language)⌝ : ℕ) ↔
      Entailment.Consistent PA194PAeq.ordinaryPAeq := by
    rw [Entailment.consistent_iff_unprovable_bot]
    exact not_congr provable_iff_provable
  exact hmap.symm.trans hs
#print axioms ordinary_q_standard
end PA194OrdinaryNativeConsistency
