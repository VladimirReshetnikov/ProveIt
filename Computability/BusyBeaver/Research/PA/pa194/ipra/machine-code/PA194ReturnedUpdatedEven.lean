import PA194ReturnedDecrement
set_option autoImplicit false
namespace PA194ReturnedUpdatedEven
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194ReturnFileMeaning
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem updatedEven (idx n : Nat) (e : Fin (idx+2) → M) (rest : Fin (n+2) → M) (v : M) :
  ∃ r : M, F (fileCode idx) (replaceLast idx (fun i : Fin (idx+1) => e i.succ)
    (F block ![v,F (fileCode (n+1)) rest])) = r+r := by
  cases idx with
  | zero =>
    rw [fileCode,modelProjection]
    simp only [replaceLast,modelBlock]
    exact ⟨_,rfl⟩
  | succ idx =>
    rw [modelFileSucc,modelBlock]
    exact ⟨_,rfl⟩
#print axioms updatedEven
end models
end PA194ReturnedUpdatedEven
