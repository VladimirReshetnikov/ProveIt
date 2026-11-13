import PA196PATermBounds
import PA196PAFormulaBound

/-! The exact Foundation arithmetic formula recognizer has bounded witnesses
in both polarities, without additional assumptions beyond the PRA model. -/
set_option autoImplicit false
namespace PA196PAFormulaComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.PRAWitnessCalculus

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_isUFormula_sigma : WB M (isUFormula ℒₒᵣ).sigma.val :=
  PA196PAFormulaBound.wb_isUFormula_sigma PA196PATermBounds.wb_isUTermVec_sigma
    PA196PATermBounds.wb_isUTermVec_neg_pi

theorem wb_isUFormula_neg_pi : WB M (∼(isUFormula ℒₒᵣ).pi.val) :=
  PA196PAFormulaBound.wb_isUFormula_neg_pi PA196PATermBounds.wb_isUTermVec_sigma
    PA196PATermBounds.wb_isUTermVec_neg_pi

#print axioms wb_isUFormula_sigma
#print axioms wb_isUFormula_neg_pi
end PA196PAFormulaComplete
