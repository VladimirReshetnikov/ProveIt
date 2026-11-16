import ConPAISigma1Directions

/-! Transport a comparison of halting predicates established in models with
classical IΣ₁ reducts to an equivalence of nonhalting sentences in iPRA. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
namespace ConPA.Relative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRANativeForwardTheory
open ConPA.ISigma1Transfer ConPA.ISigma1Models

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

private theorem mappedHall (δ : ArithmeticSemisentence 1) (M : Type) [Nonempty M]
    [Structure language M] [Structure.Eq language M] :
    (M↓[language] ⊧ Semiformula.lMap embedding (∀⁰ ∼δ)) ↔
      ¬(M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ δ)) := by
  simpa using ConPA.Directions.hall (Semiformula.lMap embedding δ) M

/-- An open halting matrix and a mapped bounded halting matrix can be
compared in classical PRA using their universal negations. -/
theorem classical_iff (p : Semisentence language 1) (hp : p.Open)
    (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ ∃⁰ p) ↔ (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ δ)))) :
    PRA ⊢ ((∃⁰ p) 🡘 Semiformula.lMap embedding (∃⁰ δ)) := by
  obtain ⟨q, hq, hqα⟩ := DiophantineConsistency.PRABoundedPiOneUnary.unary_open δ hδ
  have hcmp : PRA ⊢ ((∀⁰ ∼p) 🡘 ∀⁰ q) := by
    apply pi_one_iff_of_models (∼p) q (by simpa using hp) hq
    intro M _ _ _ hM hr
    have hqm := models_of_provable hM hqα
    simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
      at hqm ⊢
    have hneg := (ConPA.Directions.hall p M).trans <|
      (not_congr (h M hr)).trans (mappedHall δ M).symm
    exact ⟨fun hz => hqm.1 (hneg.mp hz), fun hz => hneg.mpr (hqm.2 hz)⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hc := models_of_provable hM hcmp
  have hqm := models_of_provable hM hqα
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
    at hc hqm ⊢
  constructor
  · intro hP
    by_contra hD
    exact (ConPA.Directions.hall p M).mp
      (hc.2 (hqm.1 ((mappedHall δ M).mpr hD))) hP
  · intro hD
    by_contra hP
    exact (mappedHall δ M).mp
      (hqm.2 (hc.1 ((ConPA.Directions.hall p M).mpr hP))) hD

private theorem contrapositive (a b : Sentence language) (h : PRA ⊢ a 🡒 b)
    (hback : nativeTheory ⊢! bᴺ 🡒 ∼∼native b) :
    standardTheory ⊢ ∼native b 🡒 ∼native a := by
  have hgg : nativeTheory ⊢ aᴺ 🡒 bᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical h)
  have hnn : nativeTheory ⊢! native a 🡒 ∼∼native b :=
    Entailment.C_trans (theoryNativeForward a)
      (Entailment.C_trans (Classical.choice hgg) hback)
  have hs := Classical.choice ((DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hnn⟩)
  exact ⟨Entailment.C_trans Entailment.dni (Entailment.contra hs)⟩

/-- A relative halting proof in all covered models gives the actual native
iPRA equivalence of the two negated halting sentences. -/
theorem nonhalt_iff (p : Semisentence language 1) (hp : p.Open)
    (hpBounded : Hierarchy 𝚺 0 p) (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ ∃⁰ p) ↔ (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ δ)))) :
    standardTheory ⊢ ∼native (∃⁰ p) 🡘 ∼haltSentence δ := by
  have hclass := Classical.choice (classical_iff p hp δ hδ h)
  have hpback : nativeTheory ⊢! (∃⁰ p)ᴺ 🡒 ∼∼native (∃⁰ p) := by
    simpa only [native] using exists_backward p hpBounded
  have hleft := contrapositive _ _ ⟨Entailment.K_right hclass⟩ hpback
  have hright := contrapositive _ _ ⟨Entailment.K_left hclass⟩ (halt_backward δ hδ)
  exact ⟨Entailment.K_intro (Classical.choice hleft) (Classical.choice hright)⟩

#print axioms classical_iff
#print axioms nonhalt_iff

/-- A model-level equivalence of two bounded halting matrices transfers to PRA. -/
theorem bounded_classical_iff (δ ε : ArithmeticSemisentence 1)
    (hδ : Hierarchy 𝚺 0 δ) (hε : Hierarchy 𝚺 0 ε)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ δ)) ↔
          (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ ε)))) :
    PRA ⊢ (Semiformula.lMap embedding (∃⁰ δ) 🡘 Semiformula.lMap embedding (∃⁰ ε)) := by
  obtain ⟨p, hp, hpProof⟩ := DiophantineConsistency.PRABoundedPiOneUnary.unary_open δ hδ
  obtain ⟨q, hq, hqProof⟩ := DiophantineConsistency.PRABoundedPiOneUnary.unary_open ε hε
  have common : PRA ⊢ ((∀⁰ p) 🡘 ∀⁰ q) := by
    apply pi_one_iff_of_models p q hp hq
    intro M _ _ _ hM reduct
    have hpM := models_of_provable hM hpProof
    have hqM := models_of_provable hM hqProof
    simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
      at hpM hqM ⊢
    have same := (mappedHall δ M).trans ((not_congr (h M reduct)).trans (mappedHall ε M).symm)
    exact ⟨fun a => hqM.1 (same.mp (hpM.2 a)), fun b => hpM.1 (same.mpr (hqM.2 b))⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hc := models_of_provable hM common
  have hpM := models_of_provable hM hpProof
  have hqM := models_of_provable hM hqProof
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
    at hc hpM hqM ⊢
  constructor
  · intro hD
    by_contra hE
    exact (mappedHall δ M).mp (hpM.2 (hc.2 (hqM.1 ((mappedHall ε M).mpr hE)))) hD
  · intro hE
    by_contra hD
    exact (mappedHall ε M).mp (hqM.2 (hc.1 (hpM.1 ((mappedHall δ M).mpr hD)))) hE

/-- Transfer a model comparison of two bounded halting predicates to iPRA nonhalting. -/
theorem bounded_nonhalt_iff (δ ε : ArithmeticSemisentence 1)
    (hδ : Hierarchy 𝚺 0 δ) (hε : Hierarchy 𝚺 0 ε)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ δ)) ↔
          (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ ε)))) :
    standardTheory ⊢ ∼haltSentence δ 🡘 ∼haltSentence ε := by
  have proof := Classical.choice (bounded_classical_iff δ ε hδ hε h)
  have left := contrapositive _ _ ⟨Entailment.K_right proof⟩ (halt_backward δ hδ)
  have right := contrapositive _ _ ⟨Entailment.K_left proof⟩ (halt_backward ε hε)
  exact ⟨Entailment.K_intro (Classical.choice left) (Classical.choice right)⟩

#print axioms bounded_nonhalt_iff
end ConPA.Relative
