import PA194RegisterFile
import PA194TwelveThirteenCompose
import PA194ZeroRuns
set_option autoImplicit false
namespace PA194RegisterEngine
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194TwelveThirteenCompose
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- Dense state 12 traverses the first register block of an encoded file,
turning it into zeros and entering state 13. The number of remaining
registers is fixed standard syntax; all values and the suffix are arbitrary
model elements. -/
theorem modelFirstRegister (n : Nat) (e : Fin (n+2) → M) (left : M) :
    F PA194Stepper.stepper ![((1 : M)+1)+e 0,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![left,F (fileCode (n+1)) e]]] =
    F pairCode ![TableDispatch.modelNumeral M 13,
      F pairCode ![F zeros ![e 0,(left+left)+(left+left)],F (fileCode n) (fun i => e i.succ)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let tail := F (fileCode n) (fun i => e i.succ)
  have hz (x : M) : F zeros ![(1 : M),x] = x+x := by
    have hs : F Code.succ (fun _ => (0 : M)) = (1 : M) := by
      have hh := (modelAddOne (0 : M)).symm
      change F Code.succ (fun _ => (0 : M)) = (0 : M)+1 at hh
      simpa using hh
    have h := modelZerosSucc (0 : M) x
    rw [modelZerosZero,hs] at h
    exact h
  have ho : F ones ![e 0+1,tail] = F ones ![e 0,tail]+F ones ![e 0,tail]+1 := by
    change F ones ![F addCode ![e 0,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  have hf : F (fileCode (n+1)) e =
      (F ones ![e 0,tail]+F ones ![e 0,tail]+1)+(F ones ![e 0,tail]+F ones ![e 0,tail]+1) := by
    rw [modelFileSucc,modelBlock,ho]
  have h := modelTwoScans (1 : M) (e 0) left tail
  rw [hz,hz] at h
  rw [hf]
  exact h
#print axioms modelFirstRegister
end models
end PA194RegisterEngine
