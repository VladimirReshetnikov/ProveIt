import PA194ContradictionTranslation
import PA194SourcePolarity
/-! The negative output at the distinguished source contradiction code is
the quote of the fixed standard formula negated by IΣ₁. -/
set_option autoImplicit false
namespace PA194ContradictionNegative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PA194ContradictionTranslation PA194SourceOutputWF PA194SourcePolarity
  PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem negative_code_one : π₂ (F fixedTranslation (fun _ => (1 : M))) = (⌜∼contradiction⌝ : M) := by
  have h := fixed_all_pol (M := M) 1
  change π₂ (F fixedTranslation (fun _ => (1 : M))) =
    Bootstrapping.neg ℒₒᵣ (π₁ (F fixedTranslation (fun _ => (1 : M)))) at h
  rw [positive_code_one] at h
  rw [h]
  change (∼(⌜contradiction⌝ : Bootstrapping.Semiformula M ℒₒᵣ 0)).val =
    (⌜∼contradiction⌝ : Bootstrapping.Semiformula M ℒₒᵣ 0).val
  simp
#print axioms negative_code_one
end models
end PA194ContradictionNegative
