import PA194OrdinaryStandardConsistency
import PA194OrdinaryModelConsistency
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194OrdinaryNativeConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula
open ConPA.ISigma1Models
open DiophantineConsistency.StrictSigmaOneInduction
noncomputable def ordinaryMatrix : Semisentence language 1 := Classical.choose ordinary_matrix_exists
theorem ordinaryMatrix_open : ordinaryMatrix.Open := (Classical.choose_spec ordinary_matrix_exists).1
theorem ordinaryMatrix_calibration : PRA ⊢
    (Semiformula.lMap embedding (∀⁰ ∼bnd ordinaryRefutation) 🡘 ∀⁰ ordinaryMatrix) :=
  (Classical.choose_spec ordinary_matrix_exists).2.1
noncomputable def nativeBoundedOrdinaryConsistency : Sentenceᵢ language := ∼native (∃⁰ ∼ordinaryMatrix)
theorem ordinary_implies_PA_native :
    standardTheory ⊢ nativeBoundedOrdinaryConsistency 🡒 nativePAConsistency :=
  (Classical.choose_spec ordinary_matrix_exists).2.2
local instance : Structure language ℕ := natStructure
theorem ordinaryMatrix_standard :
    (∀⁰ ordinaryMatrix).Evalb (M := ℕ) ![] ↔ Entailment.Consistent PA194PAeq.ordinaryPAeq :=
  ordinary_q_standard ordinaryMatrix ordinaryMatrix_calibration
#print axioms ordinaryMatrix_open
#print axioms ordinaryMatrix_calibration
#print axioms ordinary_implies_PA_native
#print axioms ordinaryMatrix_standard
end PA194OrdinaryNativeConsistency
