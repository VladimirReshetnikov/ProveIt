import DiophantineConsistency.PRAModelIOpenPairing
set_option autoImplicit false
namespace DiophantineConsistency.PRAPairBoundConversion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAModelIOpenPairing

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelBoundSucc (t c : M)
    (h : ¬Structure.rel (L := language) Language.ORing.Rel.lt ![t,c]) :
    Structure.rel (L := language) Language.ORing.Rel.lt
      ![c,Structure.func (L := language) addCode ![t,Structure.func (L := language) oneCode Fin.elim0]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  change ¬t < c at h
  change c < t+1
  exact lt_succ_iff_le.mpr (le_of_not_gt h)
end models
end DiophantineConsistency.PRAPairBoundConversion
