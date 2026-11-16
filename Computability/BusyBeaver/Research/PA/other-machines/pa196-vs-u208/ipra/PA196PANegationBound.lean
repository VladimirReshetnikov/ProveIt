import PA196PAFormulaRecBound
import DiophantineConsistency.PRAWitnessFormulaFunctions

/-! The actual arithmetic-language negation graph has a witness bound in
every classical PRA model in the primitive-recursive language. -/
set_option autoImplicit false
namespace PA196PANegationBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
open PRAWitnessFormulaFunctions

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_negGraph : WB M (negGraph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [negGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (PA196PAFormulaRecBound.wb_result negConstructions neg_shape neg_clauses)

#print axioms wb_negGraph
end PA196PANegationBound
