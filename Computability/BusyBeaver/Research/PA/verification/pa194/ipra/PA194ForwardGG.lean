import PA194Bounded
import DiophantineConsistency.IPRAPA196Consistency
import DiophantineConsistency.IPRABoundedInduction
import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.IPRAImpGG
import DiophantineConsistency.IPRANativeDisjunctionWitness

/-! Conditional transfer of a *classical PRA* machine reduction into iPRA.
The classical reduction itself is not proved here. -/
set_option autoImplicit false
noncomputable section
namespace PA194ForwardGG
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeFormulaRew
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRAExistentialComparison
open DiophantineConsistency.IPRANativeForwardTheory DiophantineConsistency.IPRANativeDisjunctionWitness
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def matrix (φ : Semisentence language 1) : Semisentenceᵢ language 1 := φᴺ 🡒 native φ

def matrix_all (φ : Semisentence language 1) (hφ : Hierarchy 𝚺 0 φ) :
    nativeTheory ⊢! ∀⁰ matrix φ := by
  have hc : nativeTheory ⊢! ∀⁰* matrix φ := by
    apply closeFamily 1 (matrix φ)
    intro v
    have hv : ![v 0] = v := by
      funext i
      cases i using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
    have h := DiophantineConsistency.IPRABoundedInduction.backward φ hφ ![v 0]
    simpa only [matrix, LogicalConnective.HomClass.map_imply,
      Semiformula.rew_doubleNegation, native_rew, hv] using h
  simpa only [allClosure_succ, allClosure_zero] using hc

def exists_backward (φ : Semisentence language 1) (hφ : Hierarchy 𝚺 0 φ) :
    nativeTheory ⊢! (∃⁰ φ)ᴺ 🡒 ∼∼(∃⁰ native φ) :=
  theoryExistsCompare φ (matrix_all φ hφ)

def haltMatrix : Semisentence language 1 := .rel .eq ![PA194Bounded.boundedTerm, .func oneCode Fin.elim0]
def haltClassical : Sentence language := ∃⁰ haltMatrix

theorem haltMatrix_bounded : Hierarchy 𝚺 0 haltMatrix := by
  exact Hierarchy.rel _ _ _ _

def halt_backward : nativeTheory ⊢! haltClassicalᴺ 🡒 ∼∼PA194Bounded.haltSentence := by
  simpa only [haltClassical, haltMatrix, native, PA194Bounded.haltSentence] using
    exists_backward haltMatrix haltMatrix_bounded

/-- The explicit hypothesis is the missing classical PRA reduction. -/
theorem forward_of_classical_pra
    (h : PRA ⊢ mappedPARefutation 🡒 haltClassical) :
    standardTheory ⊢ nativePARefutation 🡒 ∼∼PA194Bounded.haltSentence := by
  have hgg : nativeTheory ⊢ mappedPARefutationᴺ 🡒 haltClassicalᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical h)
  have hnative : nativeTheory ⊢! nativePARefutation 🡒 ∼∼PA194Bounded.haltSentence :=
    Entailment.C_trans (theoryNativeForward mappedPARefutation)
      (Entailment.C_trans (Classical.choice hgg) halt_backward)
  exact (DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hnative⟩

#print axioms forward_of_classical_pra
end PA194ForwardGG
