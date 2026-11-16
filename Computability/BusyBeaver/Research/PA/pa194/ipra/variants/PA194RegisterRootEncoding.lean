import PA194SourceContracts
import PA194RegisterRoot
import PA194HXRootEncoding

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 9000000
set_option linter.unusedSectionVars false

namespace PA194RegisterRootEncoding
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ZeroRuns PA194Path27Header TableDispatch PackedRootModel
open ConPA.Machine ConPA.Machine.Compressed
open PA194RegisterRoot PA194SourceContracts PA194HXRootEncoding
open M6.Runtime

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem numeralCast (n : Nat) : modelNumeral M n = (n : M) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PA194FiniteControls.modelNumeralSucc,ih,Nat.cast_succ]

theorem root_eq {label : Nat → Nat} (control : label 84 = 24)
    (gap : M) (box : BoxSt → M) (i extra : Nat) (effect : Eff) :
    root label PA194SourceProgram.path gap box i extra effect =
      frame i (gap+modelNumeral M (48+extra-(PA194SourceProgram.path i).length)) (box (.plain effect)) := by
  simp only [PA194SourceContracts.root,PA194RuntimeContracts.rootFrame,encode,scanFrame,
    frame,PA194HXRootEncoding.packBits,packSegments,runLength,Nat.cast_one,one_mul,control,numeralCast,
    modelPairCode, ↓reduceIte]
  rw [modelZeros_eq]
  simp [ConPA.Machine.Compressed.push,two_mul,add_comm]

#print axioms root_eq
end models
end PA194RegisterRootEncoding
