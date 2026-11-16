import PA194RegisterDecrement

set_option autoImplicit false
set_option maxRecDepth 30000
set_option linter.unusedSectionVars false

namespace PA194RegisterMark
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194CompressedBoxFiles PA194RegisterDecrement
open ConPA.Machine ConPA.Machine.Compressed

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem markOracle {T : Table} (rows : GenericMark.Rows T) (p : Fin 9)
    (a : Fin 11 → M) (left : M) :
    Reach T (scanFrame true (rows.control p.val) left (file a))
      (scanFrame false (GenericMark.returnControl rows p.val) (markedFileValue p a) left) := by
  have update : Function.update a (slot p) (a (slot p)) = a := by
    funext i
    by_cases h : i = slot p
    · subst i
      simp
    · simp [Function.update_of_ne h]
  have input := ordinary_eq_file p a (a (slot p))
  rw [update] at input
  have length : (before p a).length = p.val := List.length_ofFn
  have result := GenericMark.mark rows (before p a) (by rw [length]; exact p.isLt)
    (a (slot p)) left (rest p a)
  rw [length, ← input, ← marked_eq_file p a] at result
  exact reachable result

#print axioms markOracle
end models
end PA194RegisterMark
