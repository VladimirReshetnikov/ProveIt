import PA194RegisterPermutation
import PA194RegisterEngine
set_option autoImplicit false
namespace PA194SourceFileEngine
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194RegisterEngine PA194RegisterPermutation PA194ZeroRuns
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- The first physical slot is logical register 2; the remaining nine
physical blocks and suffix are retained exactly. -/
theorem modelFirstSourceSlot (e : Fin 11 → M) (left : M) :
    F PA194Stepper.stepper ![((1 : M)+1)+e 2,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![left,F sourceFileCode e]]] =
    F pairCode ![TableDispatch.modelNumeral M 13,
      F pairCode ![F zeros ![e 2,(left+left)+(left+left)], F (fileCode 9) (fun i => physicalArgs e i.succ)]] := by
  rw [modelSourceFile]
  have h := modelFirstRegister 9 (physicalArgs e) left
  exact h
#print axioms modelFirstSourceSlot
end models
end PA194SourceFileEngine
