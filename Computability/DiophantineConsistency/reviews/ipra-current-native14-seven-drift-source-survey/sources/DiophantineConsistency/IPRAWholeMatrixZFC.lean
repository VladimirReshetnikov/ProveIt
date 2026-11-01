import DiophantineConsistency.IPRAOpenDisjunctionWitness
import DiophantineConsistency.IPRAFoundationZFCMatrixComparison
import DiophantineConsistency.IPRAZFCRefutationBoundGG
/-! Exact ZFC comparison from the whole bounded-refutation matrix, with its witness bound discharged. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAWholeMatrixZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.IPRAFoundationZFCWitnessBound DiophantineConsistency.IPRAFoundationZFCMappedNegation
open DiophantineConsistency.IPRAFoundationZFCMatrixComparison DiophantineConsistency.IPRANativeDisjunctionWitness
open DiophantineConsistency.IPRATheoryHilbertBridge

def matrix : Semisentenceᵢ language 1 :=
  (Semiformula.lMap embedding (bnd rho))ᴺ 🡒 native (Semiformula.lMap embedding (bnd rho))

def fromMatrix (h : nativeTheory ⊢! ∀⁰ matrix) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding :=
  mappedZFCWithMatrix embedding DiophantineConsistency.IPRAZFCRefutationBoundGG.refutation_bound_gg_proof h

def fromOpenFamily (h : ∀ t : Term language ℕ,
    extended nativeTheory ⊢! Rew.embSubsts ![t] ▹ matrix) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding := by
  apply fromMatrix
  have hc : nativeTheory ⊢! ∀⁰* matrix := by
    apply closeFamily 1 matrix
    intro v
    have hv : ![v 0] = v := by
      funext i
      cases i using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
    simpa only [hv] using h (v 0)
  simpa only [allClosure_succ, allClosure_zero] using hc
end DiophantineConsistency.IPRAWholeMatrixZFC
