import PA194ThresholdCycle
import PA194PositiveThreshold
import PA194HeaderController
import PA194PositiveMarkerRoute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194HeaderTo61
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveThreshold PA194HeaderController PA194PositiveMarkerRoute PA194ThresholdCycle PA194IncrementDispatch
open PA194MarkAll PA194CarryFile PA194RegisterFile PA194ReturnFile PA194MarkerScan
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem nextHeaderTo61 (u z : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let l := (xx+xx)+(xx+xx)+1
    let a0 := l+l+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let s := (1 : M)+(z+z)+(z+z)
    let p := F ones ![modelNumeral M 3,s]
    let w := p+p+1
    let c := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((c+modelNumeral M 3)+modelNumeral M 4)+1,
      F pairCode ![modelNumeral M 17,F pairCode ![h,(w+w)+(w+w)+1]]] =
    F pairCode ![modelNumeral M 61,F pairCode ![a3+a3,z]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let l := (xx+xx)+(xx+xx)+1
  let s := (1 : M)+(z+z)+(z+z)
  let p := F ones ![modelNumeral M 3,s]
  let w := p+p+1
  let c := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let z0 := u+u
  let z1 := z0+z0
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let l64 := z4+z4
  have hg : g = (l64+l64)+(l64+l64) := by
    dsimp only [g]
    rw [zerosTwo, ←zerosSix]
  have hc := markerTo24 ⟨1,by decide⟩ (modelNumeral M 1) u (w+w)
  dsimp only at hc
  simp only [onesOne] at hc
  rw [←hg] at hc
  change F PA194Stepper.stepper ![c,F pairCode ![modelNumeral M 17,F pairCode ![h,(w+w)+(w+w)+1]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,(w+w)+(w+w)+1]] at hc
  have hd := threeTo35 h p
  dsimp only at hd
  let q0 := (z+z)+(z+z)+1
  let q1 := q0+q0+1
  let q2 := q1+q1+1
  let q3 := q2+q2+1
  have hp : p = q3 := by
    dsimp only [p,s,q0,q1,q2,q3]
    rw [onesThree]
    simp only [add_assoc,add_comm,add_left_comm]
  have hs := shortTraverse4 l (z+z)
  dsimp only at hs
  change F PA194Stepper.stepper ![modelNumeral M 4,F pairCode ![modelNumeral M 35,F pairCode ![l,q3]]] = _ at hs
  rw [←hp] at hs
  let a0 := l+l+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2+1
  have hb := shortBoundary (⟨4,by decide⟩ : Fin 5) a3 z
  have hb' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 43,F pairCode ![a3,z+z]]) =
      F pairCode ![modelNumeral M 61,F pairCode ![a3+a3,z]] := by
    simpa [shortControl,shortExit] using hb
  change F PA194Stepper.stepper ![F addCode ![((c+modelNumeral M 3)+modelNumeral M 4),F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![c+modelNumeral M 3,modelNumeral M 4],_]) = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![modelNumeral M 4,F PA194Stepper.stepper ![F addCode ![c,modelNumeral M 3],_]]) = _
  rw [PA194StepperCompose.modelStepperCompose,hc,hd,hs,hb']
#print axioms nextHeaderTo61
end models
end PA194HeaderTo61
