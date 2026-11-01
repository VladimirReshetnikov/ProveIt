import DiophantineConsistency.StrictSigmaOneInduction
import DiophantineConsistency.FoundationHAConsistencyNormalization
import DiophantineConsistency.ParsonsHierarchyMap
import DiophantineConsistency.PRABoundedFormula
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.PRARhoBoundedCharacteristic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAFiniteFunctionCodes PRACharacteristicBit PRABoundedCharacteristic PRABoundedFormula
open FoundationHAConsistencyNormalization StrictSigmaOneInduction

theorem bounded_rho : Hierarchy 𝚺 0 (Semiformula.lMap embedding (bnd rho)) := by
  apply ParsonsHierarchyMap.hierarchy
  exact hierarchy_bnd rho_sigma_one (by decide) (by intro _; rfl)

theorem rho_characteristic :
    ∃ c : Code 1, Primrec (eval c) ∧ PRA ⊢ bitSentence c ∧
      PRA ⊢ oneCorrectSentence c (Semiformula.lMap embedding (bnd rho)) := by
  exact PRA_proves_boundedBooleanCharacteristic _ bounded_rho
#print axioms bounded_rho
#print axioms rho_characteristic
end DiophantineConsistency.PRARhoBoundedCharacteristic
