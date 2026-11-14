import PA194MarkerSkip
import PA194PrefixFile
import PA194OnesCommute
import PA194MarkDelimiter
set_option autoImplicit false
namespace PA194MarkerPrefix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAModelIOpenPairing PA194CarryFile PA194RegisterFile PA194UnaryRuns PA194MarkerScan PA194MarkerSkip PA194OnesCommute
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelMarkerPrefix (n : Nat) (bound : n < 9) (e : Fin (n+1) → M) (l : M) :
    F PA194Stepper.stepper ![F (costCode n) e,
      F pairCode ![TableDispatch.modelNumeral M (markerControl ⟨n,bound⟩),F pairCode ![l,F (fileCode n) e]]] =
    F pairCode ![TableDispatch.modelNumeral M (markerControl ⟨0,by decide⟩),
      F pairCode ![F (PA194PrefixFile.leftCode n) (Fin.cases l e),e (Fin.last n)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n generalizing l with
  | zero =>
    rw [modelCostZero]
    have hz := PA194Stepper.modelStepperZero (F pairCode ![TableDispatch.modelNumeral M (markerControl ⟨0,by decide⟩),F pairCode ![l,F (fileCode 0) e]])
    change F PA194Stepper.stepper ![(0 : M),_] = _ at hz
    rw [hz]
    change F pairCode ![_,F pairCode ![l,F (.proj 0) e]] = _
    rw [modelProjection,PA194PrefixFile.modelLeftZero]
    rfl
  | succ n ih =>
    let tail : M := F (fileCode n) (fun i => e i.succ)
    let next : M := F ones ![e 0,(l+l)+(l+l)+1]
    have hon : F ones ![e 0+1,tail] = F ones ![e 0,tail]+F ones ![e 0,tail]+1 := by
      change F ones ![F addCode ![e 0,F oneCode Fin.elim0],tail] = _
      rw [modelAddOne,modelOnesSucc]
    rw [modelCostSucc,modelFileSucc,modelBlock,hon]
    have htime : ((1 : M)+1)+e 0 = 1+(e 0+1) := by simp only [add_assoc,add_comm,add_left_comm]
    rw [htime]
    change F PA194Stepper.stepper ![F addCode ![(1 : M)+(e 0+1),F (costCode n) (fun i => e i.succ)],_] = _
    rw [PA194StepperCompose.modelStepperCompose]
    have hi : n < 8 := by omega
    have hc := modelMarkerSkipCell ⟨n,hi⟩ (e 0) l tail
    dsimp only at hc
    have hf : (⟨n,hi⟩ : Fin 8).succ = (⟨n+1,bound⟩ : Fin 9) := by apply Fin.ext; rfl
    rw [hf] at hc
    rw [hc]
    have hleft : F ones ![e 0+1,l+l] = next := by
      dsimp [next]
      have hc := modelOnesCommute (e 0) (l+l)
      change F ones ![F addCode ![e 0,F oneCode Fin.elim0],l+l] = _
      rw [modelAddOne,modelOnesSucc,hc]
    rw [hleft]
    have hcast : (⟨n,hi⟩ : Fin 8).castSucc = (⟨n,by omega⟩ : Fin 9) := by apply Fin.ext; rfl
    rw [hcast]
    have hr := ih (by omega) (fun i => e i.succ) next
    dsimp only [next,tail] at hr
    rw [hr,PA194PrefixFile.modelLeftSucc]
    rfl
theorem modelMarkerPrefixAndDelimiter (n : Nat) (bound : n < 9)
    (e : Fin (n+1) → M) (l t : M)
    (ht : e (Fin.last n) = (t+t+1)+(t+t+1)) :
    let x := F (PA194PrefixFile.leftCode n) (Fin.cases l e)
    F PA194Stepper.stepper ![F (costCode n) e + TableDispatch.modelNumeral M 3,
      F pairCode ![TableDispatch.modelNumeral M (markerControl ⟨n,bound⟩),F pairCode ![l,F (fileCode n) e]]] =
    F pairCode ![TableDispatch.modelNumeral M 15,F pairCode ![F halfCode (fun _ => x),
      F parityCode (fun _ => x)+((t+t)+(t+t))+((t+t)+(t+t))]] := by
  change F PA194Stepper.stepper ![F addCode ![F (costCode n) e,TableDispatch.modelNumeral M 3],_] = _
  rw [PA194StepperCompose.modelStepperCompose,modelMarkerPrefix n bound e l,ht]
  change F PA194Stepper.stepper ![TableDispatch.modelNumeral M 3,F pairCode ![TableDispatch.modelNumeral M 113,F pairCode ![F (PA194PrefixFile.leftCode n) (Fin.cases l e),(t+t+1)+(t+t+1)]]] = _
  exact PA194MarkDelimiter.modelMarkDelimiter _ _
#print axioms modelMarkerPrefixAndDelimiter
#print axioms modelMarkerPrefix
end models
end PA194MarkerPrefix
