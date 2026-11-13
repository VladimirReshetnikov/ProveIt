import PA196ForwardGG
import DiophantineConsistency.IPRABoundedMappedErasure
import DiophantineConsistency.IPRARefutationWitnessBridge
import DiophantineConsistency.ParsonsHierarchyMap

/-! Conditional transfer of a classical PRA reverse reduction. Besides the
reduction, this explicitly assumes a classical PRA witness bound for the exact
Foundation PA-refutation predicate. No unconditional reverse theorem is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace PA196ReverseGG
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeFormulaRew
open DiophantineConsistency.IPRANativeForwardTheory DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.IPRARefutationWitnessBridge
open PA196ForwardGG
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

attribute [local irreducible] paRefutation

def boundedPARefutation : Sentence language :=
  Semiformula.lMap embedding (∃⁰ bnd paRefutation)

theorem paBoundedMatrix : Hierarchy 𝚺 0 (Semiformula.lMap embedding (bnd paRefutation)) := by
  apply DiophantineConsistency.ParsonsHierarchyMap.hierarchy
  exact hierarchy_bnd paRefutation_sigma_one (by decide) (by intro _; rfl)

def bounded_compare : nativeTheory ⊢! boundedPARefutationᴺ 🡒 ∼∼native boundedPARefutation := by
  simpa only [boundedPARefutation, Semiformula.lMap_exs, native] using
    exists_backward (Semiformula.lMap embedding (bnd paRefutation)) paBoundedMatrix

def bounded_erase : nativeTheory ⊢! native boundedPARefutation 🡒 native mappedPARefutation := by
  have h := DiophantineConsistency.IPRABoundedMappedErasure.existsErasure
    (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) embedding paRefutation
  apply Theoryᵢ.ofHilbert
  simpa only [boundedPARefutation, mappedPARefutation, Semiformula.lMap_emb,
    native_rew, LogicalConnective.HomClass.map_imply] using h

/-- This is the fixed exact PA-refutation witness bound still needing proof. -/
def BoundCertificate : Prop :=
  PRA ⊢ Semiformula.lMap embedding (paRefutation 🡒 ∃⁰ bnd paRefutation)

def refutation_backward (hb : BoundCertificate) :
    nativeTheory ⊢! mappedPARefutationᴺ 🡒 ∼∼nativePARefutation := by
  unfold BoundCertificate at hb
  have hclass : PRA ⊢ mappedPARefutation 🡒 boundedPARefutation := by
    simpa only [mappedPARefutation, boundedPARefutation, LogicalConnective.HomClass.map_imply] using hb
  have hgg : nativeTheory ⊢ mappedPARefutationᴺ 🡒 boundedPARefutationᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical hclass)
  exact backwardOfWitness mappedPARefutation boundedPARefutation
    (Classical.choice hgg) bounded_compare bounded_erase

/-- Both classical PRA hypotheses are explicit: the reverse reduction and a
witness bound for the actual Foundation PA refutation predicate. -/
theorem reverse_of_classical_pra
    (h : PRA ⊢ haltClassical 🡒 mappedPARefutation) (hb : BoundCertificate) :
    standardTheory ⊢ PA196Bounded.haltSentence 🡒 ∼∼nativePARefutation := by
  have hgg : nativeTheory ⊢ haltClassicalᴺ 🡒 mappedPARefutationᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical h)
  have hf : nativeTheory ⊢! PA196Bounded.haltSentence 🡒 haltClassicalᴺ := by
    simpa only [haltClassical, haltMatrix, native, PA196Bounded.haltSentence] using
      theoryNativeForward haltClassical
  have hnative : nativeTheory ⊢! PA196Bounded.haltSentence 🡒 ∼∼nativePARefutation :=
    Entailment.C_trans hf (Entailment.C_trans (Classical.choice hgg) (refutation_backward hb))
  exact (DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hnative⟩

#print axioms refutation_backward
#print axioms reverse_of_classical_pra
end PA196ReverseGG
