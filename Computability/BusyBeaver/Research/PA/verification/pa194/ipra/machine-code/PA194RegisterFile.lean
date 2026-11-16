import PA194UnaryRuns
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
namespace PA194RegisterFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PA194UnaryRuns PA194BinaryDouble

def blockBody : Code 2 := bin ones (unary .succ (.proj 0)) (.proj 1)
def block : Code 2 := bin addCode blockBody blockBody

def fileCode : (n : Nat) → Code (n+1)
  | 0 => .proj 0
  | n+1 => bin block (.proj 0)
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

theorem modelBlock (v tail : M) : F block ![v,tail] =
    F ones ![v+1,tail] + F ones ![v+1,tail] := by
  simp only [block,blockBody,modelBin,modelUnary,modelProjection,Matrix.cons_val_zero,
    Matrix.cons_val_one,←modelAddOne]
  rfl

theorem modelFileZero (tail : M) : F (fileCode 0) ![tail] = tail := by
  rw [fileCode,modelProjection]
  rfl

theorem modelFileSucc (n : Nat) (e : Fin (n+2) → M) :
    F (fileCode (n+1)) e = F block ![e 0,F (fileCode n) (fun i => e i.succ)] := by
  rw [fileCode,modelBin,modelProjection,modelComposition,getCode_pack]
  have he : (fun i : Fin (n+1) => F (.proj i.succ) e) = fun i => e i.succ := by
    funext i
    exact modelProjection i.succ e
  rw [he]
/-- A fixed standard number of register blocks, with arbitrary model-valued
register contents and suffix. -/
noncomputable def fileValue : (n : Nat) → (Fin (n+1) → M) → M
  | 0,e => e 0
  | n+1,e =>
    let tail := fileValue n (fun i => e i.succ)
    F ones ![e 0+1,tail] + F ones ![e 0+1,tail]

theorem modelFileValue (n : Nat) (e : Fin (n+1) → M) :
    F (fileCode n) e = fileValue n e := by
  induction n with
  | zero =>
    change F (.proj 0) e = e 0
    exact modelProjection 0 e
  | succ n ih =>
    rw [modelFileSucc,modelBlock,ih]
    rfl

#print axioms modelFileValue
#print axioms modelBlock
#print axioms modelFileSucc
end models
end PA194RegisterFile
