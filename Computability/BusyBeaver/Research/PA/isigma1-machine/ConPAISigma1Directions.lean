import ConPAUnconditional
import DiophantineConsistency.PRAPiOneImplication

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace ConPA.Directions
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeForwardTheory
open DiophantineConsistency.PRAPiOneImplication DiophantineConsistency.StrictSigmaOneInduction
open ConPA.ISigma1Transfer ConPA.ISigma1Models ConPA.Unconditional
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem pi_one_imp_of_models (p q : Semisentence language 1) (hp : p.Open) (hq : q.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M → M↓[language] ⊧ implication p q) :
    PRA ⊢ implication p q := by
  have hn : PRA ⊢ normal p q :=
    open_existential_of_models (matrix p q) (matrix_open p q hp hq) (by
      intro M _ _ _ hM hr
      exact (model_equiv p q).mp (h M hr))
  exact (proves_normal_iff p q).mpr hn

theorem hall (halt : Semisentence language 1) (M : Type) [Nonempty M]
    [Structure language M] [Structure.Eq language M] :
    (M↓[language] ⊧ ∀⁰ ∼halt) ↔ ¬(M↓[language] ⊧ ∃⁰ halt) := by
  rw [models_iff, models_iff]
  exact (evalb_all_neg halt).trans
    ⟨fun h hex => by obtain ⟨x, hx⟩ := (evalb_ex halt).mp hex; exact h x hx,
      fun h x hx => h ((evalb_ex halt).mpr ⟨x, hx⟩)⟩

theorem classical_forward (halt : Semisentence language 1) (hopen : halt.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        (M↓[language] ⊧ mappedPARefutation) → (M↓[language] ⊧ ∃⁰ halt)) :
    PRA ⊢ (mappedPARefutation 🡒 ∃⁰ halt) := by
  obtain ⟨q, hq, hqα⟩ :=
    DiophantineConsistency.PRABoundedPiOneUnary.unary_open (bnd paRefutation) bnd_paRefutation_sigma_zero
  have hnopen : (∼halt).Open := by simpa using hopen
  have hcmp : PRA ⊢ implication (∼halt) q := by
    apply pi_one_imp_of_models (∼halt) q hnopen hq
    intro M _ _ _ hM hr
    have hqm := models_of_provable hM hqα
    have hmr := model_refutation (M := M) (models_of_provable hM certificate)
    simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hqm
    simp only [implication, Semantics.Imp.models_imply]
    intro ha
    by_contra hnq
    have hp : M↓[language] ⊧ mappedPARefutation := hmr.mpr (fun hx => hnq (hqm.1 hx))
    exact (hall halt M).mp ha (h M hr hp)
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hc := models_of_provable hM hcmp
  simp only [implication, Semantics.Imp.models_imply] at hc
  have hqm := models_of_provable hM hqα
  have hmr := model_refutation (M := M) (models_of_provable hM certificate)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hqm ⊢
  intro hp
  by_contra hnh
  exact (hmr.mp hp) (hqm.2 (hc ((hall halt M).mpr hnh)))

theorem classical_reverse (halt : Semisentence language 1) (hopen : halt.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        (M↓[language] ⊧ ∃⁰ halt) → (M↓[language] ⊧ mappedPARefutation)) :
    PRA ⊢ ((∃⁰ halt) 🡒 mappedPARefutation) := by
  obtain ⟨q, hq, hqα⟩ :=
    DiophantineConsistency.PRABoundedPiOneUnary.unary_open (bnd paRefutation) bnd_paRefutation_sigma_zero
  have hnopen : (∼halt).Open := by simpa using hopen
  have hcmp : PRA ⊢ implication q (∼halt) := by
    apply pi_one_imp_of_models q (∼halt) hq hnopen
    intro M _ _ _ hM hr
    have hqm := models_of_provable hM hqα
    have hmr := model_refutation (M := M) (models_of_provable hM certificate)
    simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hqm
    simp only [implication, Semantics.Imp.models_imply]
    intro hq'
    refine (hall halt M).mpr ?_
    intro hhalt
    exact (hmr.mp (h M hr hhalt)) (hqm.2 hq')
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hc := models_of_provable hM hcmp
  simp only [implication, Semantics.Imp.models_imply] at hc
  have hqm := models_of_provable hM hqα
  have hmr := model_refutation (M := M) (models_of_provable hM certificate)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hqm ⊢
  intro hhalt
  refine hmr.mpr ?_
  intro hx
  exact (hall halt M).mp (hc (hqm.1 hx)) hhalt

/-- A one-way model reduction from refutation to halting yields the
nonhalting-to-consistency implication in iPRA. -/
theorem ipra_nonhalt_implies_consistency (halt : Semisentence language 1)
    (hopen : halt.Open) (hbounded : Hierarchy 𝚺 0 halt)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        (M↓[language] ⊧ mappedPARefutation) → (M↓[language] ⊧ ∃⁰ halt)) :
    standardTheory ⊢ ∼native (∃⁰ halt) 🡒 nativePAConsistency := by
  have hgg : nativeTheory ⊢ mappedPARefutationᴺ 🡒 (∃⁰ halt)ᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical (classical_forward halt hopen h))
  have hback : nativeTheory ⊢! (∃⁰ halt)ᴺ 🡒 ∼∼native (∃⁰ halt) := by
    simpa only [native] using exists_backward halt hbounded
  have hf : nativeTheory ⊢! nativePARefutation 🡒 ∼∼native (∃⁰ halt) :=
    Entailment.C_trans (theoryNativeForward mappedPARefutation)
      (Entailment.C_trans (Classical.choice hgg) hback)
  have hf' := Classical.choice ((DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hf⟩)
  refine ⟨?_⟩
  unfold nativePAConsistency
  exact Entailment.C_trans Entailment.dni (Entailment.contra hf')

/-- A one-way model reduction from halting to refutation yields the
consistency-to-nonhalting implication in iPRA. -/
theorem ipra_consistency_implies_nonhalt (halt : Semisentence language 1)
    (hopen : halt.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        (M↓[language] ⊧ ∃⁰ halt) → (M↓[language] ⊧ mappedPARefutation)) :
    standardTheory ⊢ nativePAConsistency 🡒 ∼native (∃⁰ halt) := by
  have hgg : nativeTheory ⊢ (∃⁰ halt)ᴺ 🡒 mappedPARefutationᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical (classical_reverse halt hopen h))
  have hr : nativeTheory ⊢! native (∃⁰ halt) 🡒 ∼∼nativePARefutation :=
    Entailment.C_trans (theoryNativeForward (∃⁰ halt))
      (Entailment.C_trans (Classical.choice hgg) (refutation_backward certificate))
  have hr' := Classical.choice ((DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hr⟩)
  refine ⟨?_⟩
  unfold nativePAConsistency
  exact Entailment.C_trans Entailment.dni (Entailment.contra hr')

#print axioms ipra_nonhalt_implies_consistency
#print axioms ipra_consistency_implies_nonhalt
#print axioms classical_forward
#print axioms classical_reverse
end ConPA.Directions
