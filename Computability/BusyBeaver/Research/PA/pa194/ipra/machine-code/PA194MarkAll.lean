import PA194MarkerPrefix
import PA194MarkerReturnPrefix
set_option autoImplicit false
namespace PA194MarkAll
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAModelIOpenPairing PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan PA194MarkerPrefix PA194MarkerReturnCell PA194MarkerReturnPrefix
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelMarkAllPositive (n : Nat) (bound : n+1 < 9)
    (e : Fin (n+2) → M) (l t : M)
    (ht : e (Fin.last (n+1)) = (t+t+1)+(t+t+1)) :
    let u := (t+t)+(t+t)
    let a := F (returnCode (n+1)) (Fin.cases u e)
    F PA194Stepper.stepper ![(F (costCode (n+1)) e+TableDispatch.modelNumeral M 3)+F (costCode (n+1)) e,
      F pairCode ![TableDispatch.modelNumeral M (markerControl ⟨n+1,bound⟩),F pairCode ![l,F (fileCode (n+1)) e]]] =
    F pairCode ![TableDispatch.modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+a+a]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let u := (t+t)+(t+t)
  change F PA194Stepper.stepper ![F addCode ![F (costCode (n+1)) e+TableDispatch.modelNumeral M 3,F (costCode (n+1)) e],_] = _
  rw [PA194StepperCompose.modelStepperCompose,modelMarkerPrefixAndDelimiter (n+1) bound e l t ht]
  have h := modelMarkerReturnPrefix n ⟨0,by decide⟩ e l u
  dsimp only at h
  have hc : returnControl (⟨0,by decide⟩ : Fin 2) = 15 := rfl
  rw [hc] at h
  exact h
#print axioms modelMarkAllPositive
end models
end PA194MarkAll
