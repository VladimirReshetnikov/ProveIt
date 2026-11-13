import DiophantineConsistency.IPRABoundedRhoZFC
import DiophantineConsistency.IPRACharacteristicTransfer
import DiophantineConsistency.IPRABoundedShape

/-! A uniform primitive-recursive characteristic for the selected bounded
Foundation refutation matrix. This does not identify a particular external
proof-checker coding or assert consistency. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASelectedMatrixCharacteristic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory
open IPRANativeFormula IPRATheoryHilbertBridge IPRACharacteristicTransfer
open IPRAFoundationZFCWitnessBound FoundationHAConsistencyNormalization
open StrictSigmaOneInduction IPRAFoundationZFCMappedNegation
open IPRAFoundationZFCMappedErasure IPRAFoundationZFCMatrixComparison
open IPRARefutationNegationTheory IPRANativeDisjunctionWitness IPRANativeForwardTheory

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

/-- One PR code decides the exact bounded matrix uniformly for all term inputs
in the extended native theory. Its existence is not a literal printed code. -/
theorem selected_matrix_characteristic : ∃ c : Code 1,
    Primrec (PRAFiniteFunctionCodes.eval c) ∧
    PRA ⊢ PRACharacteristicBit.bitSentence c ∧
    ∀ e : Fin 1 → Term language ℕ,
      extended nativeTheory ⊢ native (Rew.embSubsts e ▹ oneAtom c) 🡘
        native (Rew.embSubsts e ▹ (Semiformula.lMap embedding (bnd rho))) := by
  let φ : Semisentence language 1 := Semiformula.lMap embedding (bnd rho)
  have hφ : Hierarchy 𝚺 0 φ := IPRABoundedRhoZFC.boundedMatrix
  obtain ⟨c, hbit, hc⟩ := IPRABoundedShape.boundedCharacteristicAny φ hφ
  refine ⟨c, PRAFiniteFunctionCodes.eval_primrec c, hbit, ?_⟩
  intro e
  exact ⟨transferCorrectness c φ hc e (IPRABoundedInduction.backward φ hφ e)⟩

/-- Negating the selected refutation is equivalent to negating its bounded
matrix witness. This is a negated equivalence; no positive witness is extracted. -/
theorem selected_bounded_negation : nativeTheory ⊢
    ∼mappedNativeRefutation embedding 🡘
      ∼native (Semiformula.lMap embedding boundedRefutation) := by
  have hm : nativeTheory ⊢! ∀⁰ ((Semiformula.lMap embedding (bnd rho))ᴺ 🡒
      native (Semiformula.lMap embedding (bnd rho))) := by
    have hc : nativeTheory ⊢! ∀⁰* IPRAWholeMatrixZFC.matrix := by
      apply closeFamily 1 IPRAWholeMatrixZFC.matrix
      intro v
      have hv : ![v 0] = v := by
        funext i
        cases i using Fin.cases with
        | zero => simp
        | succ j => exact Fin.elim0 j
      simpa only [hv] using IPRABoundedRhoZFC.matrixOpen (v 0)
    simpa only [allClosure_succ, allClosure_zero, IPRAWholeMatrixZFC.matrix] using hc
  have hc := boundedComparison (T := nativeTheory) embedding hm
  have hb : nativeTheory ⊢! (Semiformula.lMap embedding rho)ᴺ 🡒
      (Semiformula.lMap embedding boundedRefutation)ᴺ := by
    simpa only [boundedRefutation, rho, PRAWitnessZFCRefutationBound.refutation] using
      IPRAZFCRefutationBoundGG.refutation_bound_gg_proof
  have hf := theoryNativeForward (T := nativeTheory) (Semiformula.lMap embedding rho)
  have he := exactErasure (T := nativeTheory) embedding
  exact ⟨theoryNegationsEquivalent _ _ he (Entailment.C_trans hf (Entailment.C_trans hb hc))⟩

#print axioms selected_matrix_characteristic
#print axioms selected_bounded_negation
end DiophantineConsistency.IPRASelectedMatrixCharacteristic
