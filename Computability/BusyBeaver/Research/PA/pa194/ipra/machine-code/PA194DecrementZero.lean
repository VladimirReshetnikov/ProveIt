import PA194RollbackFile
set_option autoImplicit false
namespace PA194DecrementZero
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAModelIOpenPairing PA194UnaryRuns PA194RegisterFile PA194CarryFile PA194ReturnFile PA194DecrementZeroCell PA194RollbackFile
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelZeroDecrement (p : Nat) (ep : Fin (p+1) → M) (l t : M)
    (hp : ep (Fin.last p) = (((t+t+1)+(t+t+1))+((t+t+1)+(t+t+1)))+(((t+t+1)+(t+t+1))+((t+t+1)+(t+t+1)))) :
    let a := t+t+1
    let b := a+a
    let d := b+b
    let f := d+d
    let u := f+(1+1)
    let cost := F (costCode p) ep
    let out := F (returnCode p) (Fin.cases u ep)
    F PA194Stepper.stepper ![(cost+TableDispatch.modelNumeral M 7)+cost,
      F pairCode ![(1 : M),F pairCode ![l,F (fileCode p) ep]]] =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+out+out]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let a := t+t+1
  let b := a+a
  let d := b+b
  let f := d+d
  let u := f+(1+1)
  change F PA194Stepper.stepper ![F addCode ![F addCode ![F (costCode p) ep,TableDispatch.modelNumeral M 7],F (costCode p) ep],_] = _
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose]
  rw [modelCarryFile,hp,modelZeroCell]
  have h := modelRollbackPrefix p ep l u
  dsimp only at h
  have he : (F parityCode (fun _ => F (leftCode p) (Fin.cases l ep))+(f+f)+(1+1)+(1+1)) =
      F parityCode (fun _ => F (leftCode p) (Fin.cases l ep))+u+u := by
    dsimp [u]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [he]
  exact h
#print axioms modelZeroDecrement
end models
end PA194DecrementZero
