import DiophantineConsistency.PRAWitnessFormulaFunctions
import DiophantineConsistency.PRAWitnessSetShiftGraph
/-! Actual set-language set-shift graph has monotone witness bounds in every candidate-PRA model. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessSetShiftCandidate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_setShiftGraph : WB M (setShiftGraph ℒₛₑₜ).val :=
  PRAWitnessSetShiftGraph.wb_setShiftGraph (PRAWitnessFormulaFunctions.wb_shiftGraph (M := M))
end DiophantineConsistency.PRAWitnessSetShiftCandidate
