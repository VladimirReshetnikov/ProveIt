import PA194OrdinaryNativeConsistency
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194OrdinaryNativeConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open ConPA.ISigma1Models ConPA.ISigma1Transfer
open LO.FirstOrder.Arithmetic.Bootstrapping
open DiophantineConsistency.StrictSigmaOneInduction
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem ordinary_q_model (hr : ReductISigma1 M) (q : Semisentence language 1)
    (hq : PRA ⊢ (Semiformula.lMap embedding (∀⁰ ∼bnd ordinaryRefutation) 🡘 ∀⁰ q)) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
    (M↓[language] ⊧ ∀⁰ q) ↔ ¬Provable PA194PAeq.ordinaryPAeq (qqFalsum : M) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hq
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hm
  have hmap : (M↓[language] ⊧ ∀⁰ q) ↔
      (M↓[language] ⊧ Semiformula.lMap embedding (∀⁰ ∼bnd ordinaryRefutation)) := ⟨hm.2,hm.1⟩
  have hmap' : (M↓[language] ⊧ ∀⁰ q) ↔ (∀⁰ ∼bnd ordinaryRefutation).Evalb (M := M) ![] := by
    constructor
    · intro h
      have hh := hmap.mp h
      rw [models_iff, PRAWitnessTransfer.eval_lMap_std] at hh
      exact hh
    · intro h
      apply hmap.mpr
      rw [models_iff, PRAWitnessTransfer.eval_lMap_std]
      exact h
  have hb := StrictPiTwoBridge.eval_bnd_iff (M := M) ordinaryRefutation_sigma
  have hnorm : (∀⁰ ∼bnd ordinaryRefutation).Evalb (M := M) ![] ↔ ¬ordinaryRefutation.Evalb (M := M) ![] := by
    rw [evalb_all_neg]
    constructor
    · intro h hp
      obtain ⟨w,hw⟩ := hb.mp hp
      exact h w hw
    · intro h w hw
      exact h (hb.mpr ⟨w,hw⟩)
  rw [hnorm] at hmap'
  have hrefl : ordinaryRefutation.Evalb (M := M) ![] ↔
      Provable PA194PAeq.ordinaryPAeq (qqFalsum : M) := by
    simp [ordinaryRefutation,provabilityPred,Sentence.quote_def]
  rw [hrefl] at hmap'
  exact hmap'
#print axioms ordinary_q_model
end models
end PA194OrdinaryNativeConsistency
