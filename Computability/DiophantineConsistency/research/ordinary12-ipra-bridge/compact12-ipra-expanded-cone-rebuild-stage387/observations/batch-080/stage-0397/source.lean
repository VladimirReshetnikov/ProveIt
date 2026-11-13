import DiophantineConsistency.IPRAWholeMatrixZFC
import DiophantineConsistency.IPRABoundedInduction
import DiophantineConsistency.ParsonsHierarchyMap

/-! Native comparison for the literal bounded Foundation ZFC refutation matrix. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRABoundedRhoZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeFormulaRew
open DiophantineConsistency.StrictSigmaOneInduction DiophantineConsistency.IPRAWholeMatrixZFC
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRAFoundationZFCMappedNegation

theorem boundedMatrix : Hierarchy 𝚺 0 (Semiformula.lMap embedding (bnd rho)) := by
  apply DiophantineConsistency.ParsonsHierarchyMap.hierarchy
  exact hierarchy_bnd rho_sigma_one (by decide) (by intro _; rfl)

def matrixOpen (t : Term language ℕ) : extended nativeTheory ⊢! Rew.embSubsts ![t] ▹ matrix := by
  have h := DiophantineConsistency.IPRABoundedInduction.backward
    (Semiformula.lMap embedding (bnd rho)) boundedMatrix ![t]
  simpa only [matrix, LogicalConnective.HomClass.map_imply,
    Semiformula.rew_doubleNegation, native_rew] using h

def zfcEquiv : nativeTheory ⊢!
    (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding :=
  fromOpenFamily matrixOpen
end DiophantineConsistency.IPRABoundedRhoZFC
