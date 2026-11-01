import DiophantineConsistency.PRAWitnessFormulaSet
import DiophantineConsistency.PRAWitnessFormulaFunctions
/-! Unconditional formula-set witness bounds in candidate-PRA models. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessFormulaSetCandidate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCalculus PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_isFormulaSet_sigma : WB M (isFormulaSet ℒₛₑₜ).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  exact PRAWitnessFormulaSet.wb_isFormulaSet_sigma
    (PRAWitnessFormulaFunctions.wb_isSemiformula_sigma (M := M))
theorem wb_isFormulaSet_neg_pi : WB M (∼(isFormulaSet ℒₛₑₜ).pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  exact PRAWitnessFormulaSet.wb_isFormulaSet_neg_pi
    (PRAWitnessFormulaFunctions.wb_isSemiformula_neg_pi (M := M))
end DiophantineConsistency.PRAWitnessFormulaSetCandidate
