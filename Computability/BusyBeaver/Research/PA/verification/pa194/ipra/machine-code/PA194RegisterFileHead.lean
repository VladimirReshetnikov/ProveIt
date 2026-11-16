import PA194RegisterFile
import PA194BinaryDouble
set_option autoImplicit false
namespace PA194RegisterFileHead
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194RegisterFile PA194UnaryRuns PA194BinaryDouble BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelFileSeparator (n : Nat) (e : Fin (n+2) → M) :
    F parityCode (fun _ => F (fileCode (n+1)) e) = (0 : M) ∧
    F halfCode (fun _ => F (fileCode (n+1)) e) = F ones ![e 0+1,F (fileCode n) (fun i => e i.succ)] := by
  rw [modelFileSucc,modelBlock]
  exact modelDouble _

theorem modelFileMandatoryOne (n : Nat) (e : Fin (n+2) → M) :
    F parityCode (fun _ => F halfCode (fun _ => F (fileCode (n+1)) e)) = (1 : M) ∧
    F halfCode (fun _ => F halfCode (fun _ => F (fileCode (n+1)) e)) = F ones ![e 0,F (fileCode n) (fun i => e i.succ)] := by
  rw [(modelFileSeparator n e).2]
  have h := modelOnesSucc (e 0) (F (fileCode n) (fun i => e i.succ))
  change F ones ![F Code.succ (fun _ => e 0),_] = _ at h
  have hs : F Code.succ (fun _ => e 0) = e 0 + 1 := (modelAddOne _).symm
  rw [hs] at h
  rw [h]
  exact modelOdd _
#print axioms modelFileSeparator
#print axioms modelFileMandatoryOne
end models
end PA194RegisterFileHead
