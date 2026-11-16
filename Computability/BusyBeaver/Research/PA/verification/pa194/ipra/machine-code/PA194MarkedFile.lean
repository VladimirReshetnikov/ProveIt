import PA194RegisterFile
import PA194SelectedCell
set_option autoImplicit false
namespace PA194MarkedFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PA194RegisterFile PA194SelectedCell PA194UnaryRuns

def twice {n : Nat} (c : Code n) : Code n := bin addCode c c
def markedBlock : Code 2 := twice (twice ones)
def markedFile : (n : Nat) → Code (n+2)
  | n => bin markedBlock (.proj 0)
      (.comp (fileCode n) (pack (n+1) (fun i => .proj i.succ)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelMarkedBlock (v tail : M) : F markedBlock ![v,tail] =
    (F ones ![v,tail]+F ones ![v,tail])+(F ones ![v,tail]+F ones ![v,tail]) := by
  simp only [markedBlock,twice,modelBin]
  rfl

theorem modelMarkedFile (n : Nat) (e : Fin (n+2) → M) :
    F (markedFile n) e = F markedBlock ![e 0,F (fileCode n) (fun i => e i.succ)] := by
  rw [markedFile,modelBin,modelProjection,modelComposition,getCode_pack]
  have he : (fun i : Fin (n+1) => F (.proj i.succ) e) = fun i => e i.succ := by
    funext i
    exact modelProjection i.succ e
  rw [he]

theorem modelSelectedMarked (n : Nat) (e : Fin (n+2) → M) (left : M) :
    F PA194Stepper.stepper ![((1 : M)+1)+e 0,F pairCode ![TableDispatch.modelNumeral M 2,
      F pairCode ![left,F (markedFile n) e]]] =
    F pairCode ![(1 : M),F pairCode ![F ones ![e 0,(left+left)+(left+left)+1],F (fileCode n) (fun i => e i.succ)]] := by
  rw [modelMarkedFile,modelMarkedBlock]
  exact modelSelectedCell (e 0) left (F (fileCode n) (fun i => e i.succ))
#print axioms modelMarkedBlock
#print axioms modelMarkedFile
#print axioms modelSelectedMarked
end models
end PA194MarkedFile
