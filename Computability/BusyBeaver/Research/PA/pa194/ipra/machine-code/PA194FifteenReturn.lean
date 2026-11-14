import PA194FourteenComposition
import PA194ZeroScanInvariant
import PA194ZerosDouble
import PA194StepperCompose
set_option autoImplicit false
namespace PA194FifteenReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194ZerosDouble
open BinaryTapeCodes PA194FourteenComposition
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelFifteenStart (n m l r : M) :
    F PA194Stepper.stepper ![(((n+1)+(m+1))+1)+1,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l,F zeros ![n,F ones ![m+1,r+r]+F ones ![m+1,r+r]+1]]]] =
    F pairCode ![TableDispatch.modelNumeral M 15,
      F pairCode ![F zeros ![m,F zeros ![n,l]],(1+(r+r)+(r+r))+(1+(r+r)+(r+r))]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := modelConnectedFifteen n (m+1) l r
  dsimp only at h
  have hsucc : F zeros ![m+1,F zeros ![n,l]+F zeros ![n,l]] =
      F zeros ![m,F zeros ![n,l]+F zeros ![n,l]] + F zeros ![m,F zeros ![n,l]+F zeros ![n,l]] := by
    change F zeros ![F addCode ![m,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelZerosSucc]
  rw [hsucc] at h
  rw [(modelDouble _).2] at h
  rw [modelZerosDouble m (F zeros ![n,l])] at h
  rw [(modelDouble _).2,(modelDouble _).1] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem modelReturn (n m l r : M) :
    F PA194Stepper.stepper ![((((n+1)+(m+1))+1)+1)+m,F pairCode ![TableDispatch.modelNumeral M 12,
      F pairCode ![l,F zeros ![n,F ones ![m+1,r+r]+F ones ![m+1,r+r]+1]]]] =
    F pairCode ![TableDispatch.modelNumeral M 15,
      F pairCode ![F zeros ![n,l],F zeros ![m,1+(r+r)+(r+r)]+F zeros ![m,1+(r+r)+(r+r)]]] := by
  change F PA194Stepper.stepper ![F addCode ![(((n+1)+(m+1))+1)+1,m],_] = _
  rw [PA194StepperCompose.modelStepperCompose,modelFifteenStart,PA194ZeroScanInvariant.modelFullScan]
#print axioms modelFifteenStart
#print axioms modelReturn
end models
end PA194FifteenReturn
