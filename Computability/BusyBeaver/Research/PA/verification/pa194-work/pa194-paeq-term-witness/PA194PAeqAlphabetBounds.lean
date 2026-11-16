import PA194PAeqLanguage
import DiophantineConsistency.PRAWitnessFormulas
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! All-model witness bounds for the actual arithmetic-language function and
relation symbol recognizers, in both polarities. These are base components for
arithmetic syntax recognition; they do not bound formula or proof coding. -/
set_option autoImplicit false
namespace PA194PAeqAlphabetBounds
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

theorem wb_isFunc : WB M PA194PAeq.language.isFunc.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  change WB M (“k f. (k=0 ∧ f=0) ∨ (k=1 ∧ f=1) ∨ (k=2 ∧ (f=2 ∨ f=3))” : ArithmeticSemisentence 2)
  wb_auto

theorem wb_neg_isFunc : WB M (∼PA194PAeq.language.isFunc.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  change WB M (∼(“k f. (k=0 ∧ f=0) ∨ (k=1 ∧ f=1) ∨ (k=2 ∧ (f=2 ∨ f=3))” : ArithmeticSemisentence 2))
  wb_auto

theorem wb_isRel : WB M PA194PAeq.language.isRel.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  change WB M (“k r. k=2 ∧ r=0” : ArithmeticSemisentence 2)
  wb_auto

theorem wb_neg_isRel : WB M (∼PA194PAeq.language.isRel.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  change WB M (∼(“k r. k=2 ∧ r=0” : ArithmeticSemisentence 2))
  wb_auto

#print axioms wb_isFunc
#print axioms wb_neg_isFunc
#print axioms wb_isRel
#print axioms wb_neg_isRel
end PA194PAeqAlphabetBounds
