import PA194DecrementPositiveCell
import PA194MarkedFile
import PA194ReturnFile
set_option autoImplicit false
namespace PA194DecrementPositive
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194MarkedFile PA194CarryFile PA194ReturnFile PA194DecrementPositiveCell
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelPositiveDecrement (p n : Nat) (ep : Fin (p+1) → M) (e : Fin (n+1) → M) (v l : M)
    (hp : ep (Fin.last p) = F markedBlock ![v+1,F (fileCode n) e]) :
    let cost := F (costCode p) ep
    let a := F block ![v,F (fileCode n) e]
    let out := F (returnCode p) (Fin.cases a ep)
    F PA194Stepper.stepper ![(cost+TableDispatch.modelNumeral M 4)+cost,
      F pairCode ![(1 : M),F pairCode ![l,F (fileCode p) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 7,F pairCode ![l,out+out+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let tail := F (fileCode n) e
  let t := F ones ![v,tail]
  let a := t+t+1
  let b := a+a
  have hs : F ones ![v+1,tail] = a := by
    change F ones ![F addCode ![v,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  have hm : F markedBlock ![v+1,tail] = b+b := by
    rw [modelMarkedBlock,hs]
  have hb : F block ![v,tail] = b := by
    rw [modelBlock,hs]
  have hsix : (b+b)+1 = b+b+1 := rfl
  change F PA194Stepper.stepper ![F addCode ![F addCode ![F (costCode p) ep,TableDispatch.modelNumeral M 4],F (costCode p) ep],_] = _
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose]
  rw [modelCarryFile,hp,hm,modelPositiveCell]
  rw [modelReturnFile]
  rw [hb]
#print axioms modelPositiveDecrement
end models
end PA194DecrementPositive
