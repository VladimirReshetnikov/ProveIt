import PA194OrdinaryNativeConsistency
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

theorem ordinary_q_map (q : Semisentence language 1)
    (hq : PRA ⊢ (Semiformula.lMap embedding (∀⁰ ∼bnd ordinaryRefutation) 🡘 ∀⁰ q)) :
    (∀⁰ ∼bnd ordinaryRefutation).Evalb (M := ℕ) ![] ↔ (∀⁰ q).Evalb (M := ℕ) ![] := by
  letI : ℕ↓[language] ⊧* PRA := nat_models_PRA
  have hm := models_of_provable (inferInstance : ℕ↓[language] ⊧* PRA) hq
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hm
  have hmap : (Semiformula.lMap embedding (∀⁰ ∼bnd ordinaryRefutation)).Evalb (M := ℕ) ![] ↔
      (∀⁰ q).Evalb (M := ℕ) ![] := by simpa [models_iff] using (Iff.intro hm.1 hm.2)
  rw [nat_formula_map] at hmap
  exact hmap
#print axioms ordinary_q_map
end PA194OrdinaryNativeConsistency
