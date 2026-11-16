import PA194FirstFourZeroTo15
import PA194MarkerReturnCell
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstFourFifteenTo17
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194MarkerReturnCell PA194BinaryDouble PA194ZeroRuns
open PRAModelIOpenPairing TableDispatch PA194MarkerScan
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem fifteenTo17 (l q : M) :
    let a := F ones ![modelNumeral M 2,l+l]
    let t := (1 : M)+q+q
    let w := F ones ![(1 : M),1+t+t]
    F PA194Stepper.stepper ![((1 : M)+1)+1,
      F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => a),
        F parityCode (fun _ => a)+(1+1)+(q+q)+(q+q)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have ho (v : M) : F ones ![(1 : M),v] = v+v+1 := by
    rw [← PA194StateOne.modelNumeralOne]
    change F ones ![F Code.succ (fun _ => modelNumeral M 0),v] = _
    rw [modelOnesSucc,show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero,PA194StateOne.modelNumeralOne]
  have htwo (v : M) : F ones ![modelNumeral M 2,v] = (v+v+1)+(v+v+1)+1 := by
    rw [show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl, modelOnesSucc,PA194StateOne.modelNumeralOne,ho]
  rw [htwo,(modelOdd ((l+l)+(l+l)+1)).1,(modelOdd ((l+l)+(l+l)+1)).2]
  have hleft : (l+l)+(l+l)+1 = F ones ![(1 : M),l+l] := (ho (l+l)).symm
  rw [hleft]
  have hr : (1 : M)+(1+1)+(q+q)+(q+q) = ((1+q+q)+(1+q+q))+1 := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hr]
  have hh := modelMarkerReturnCell (⟨0,by decide⟩ : Fin 2) (1 : M) l (1+q+q)
  rw [show returnControl (⟨0,by decide⟩ : Fin 2) = 15 from rfl] at hh
  exact hh
/-- Continue the genuine first-four zero-selected marker path to dense 17. -/
theorem markerFirstFourZeroTo17 (n : Nat) (e : Fin 2 → M) (rest : Fin (n+2) → M)
    (u : M)
    (ht : e (Fin.last 1) =
      let t := F ones ![(0 : M),F (fileCode (n+1)) rest]; (t+t+1)+(t+t+1))
    (hfirst : e 0 = modelNumeral M 4) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l64 := z4+z4
    let x := ((l64+l64)+(l64+l64))+((l64+l64)+(l64+l64))+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let q := F ones ![rest 0,F (fileCode n) (fun i => rest i.succ)]
    let t := (1 : M)+q+q
    let w := F ones ![(1 : M),1+t+t]
    ∃ time : M, F PA194Stepper.stepper ![time,
      F pairCode ![modelNumeral M (markerControl ⟨1,by decide⟩),F pairCode ![x+x+1,F (fileCode 1) e]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![a2,1+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2+1
  let q := F ones ![rest 0,F (fileCode n) (fun i => rest i.succ)]
  obtain ⟨time,hrun⟩ := PA194FirstFourZeroTo15.markerFirstFourZeroTo15 n e rest u ht hfirst
  try dsimp only at hrun
  have hnext := fifteenTo17 a3 q
  dsimp only at hnext
  rw [(modelOdd a2).1,(modelOdd a2).2] at hnext
  refine ⟨time+(((1 : M)+1)+1),?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hrun]
  exact hnext
#print axioms markerFirstFourZeroTo17
#print axioms fifteenTo17
end models
end PA194FirstFourFifteenTo17
