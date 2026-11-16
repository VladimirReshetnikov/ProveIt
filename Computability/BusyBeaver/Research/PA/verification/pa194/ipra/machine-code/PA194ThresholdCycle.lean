import PA194PositiveThreshold
import PA194HeaderController
import PA194PositiveMarkerRoute
/-! The all-model five-one threshold return and next controller cycle to dense state 42. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ThresholdCycle
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194PositiveThreshold PA194HeaderController PA194PositiveMarkerRoute
open PA194IncrementDispatch PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem thresholdCycleTo42 (u r : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let x := h+h+1
    let l := (x+x)+(x+x)+1
    let t0 := r+r+1
    let t1 := t0+t0+1
    let t2 := t1+t1+1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let a0 := l+l+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2
    let c1 := modelNumeral M 6+((modelNumeral M 3+1)+1)
    let c2 := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![(((c1+c2)+modelNumeral M 3)+modelNumeral M 3)+1,
      F pairCode ![modelNumeral M 35,F pairCode ![l,t4]]] =
    F pairCode ![modelNumeral M 42,F pairCode ![a3,r+r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let x := h+h+1
  let l := (x+x)+(x+x)+1
  let s := (1 : M)+((r+r)+(r+r))+((r+r)+(r+r))
  let p0 := s+s+1
  let p := p0+p0+1
  let a := F ones ![modelNumeral M 3,s]
  let t := a+a
  let c1 := modelNumeral M 6+((modelNumeral M 3+1)+1)
  let c2 := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have hf := thresholdReturn x r
  dsimp only at hf
  rw [(modelOdd h).1,(modelOdd h).2] at hf
  have ha : a = p+p+1 := by
    dsimp only [a,p,p0]
    rw [onesThree]
  change _ = F pairCode ![modelNumeral M 17,F pairCode ![h,(1 : M)+(a+a)+(a+a)]] at hf
  have hcomm : (1 : M)+(a+a)+(a+a) = (a+a)+(a+a)+1 := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [hcomm] at hf
  let z := u+u
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let l64 := z4+z4
  have hg : g = (l64+l64)+(l64+l64) := by
    dsimp only [g]
    rw [zerosTwo, ←zerosSix]
  have hc := markerTo24 ⟨1,by decide⟩ (modelNumeral M 1) u t
  dsimp only at hc
  simp only [onesOne] at hc
  rw [←hg] at hc
  have h3 := threeTo35 h p
  dsimp only at h3
  dsimp only [t] at hc
  rw [ha] at hf hc
  change F PA194Stepper.stepper ![c2,F pairCode ![modelNumeral M 17,F pairCode ![h,((p+p+1)+(p+p+1))+((p+p+1)+(p+p+1))+1]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,((p+p+1)+(p+p+1))+((p+p+1)+(p+p+1))+1]] at hc
  let v := (r+r)+(r+r)
  let v0 := v+v+1
  let v1 := v0+v0+1
  let v2 := v1+v1+1
  have hp : p = v2 := by
    dsimp only [p,p0,s,v,v0,v1,v2]
    simp only [add_assoc,add_comm,add_left_comm]
  let a0 := l+l+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  have ht := shortTraverse3 l v
  dsimp only at ht
  change F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 35,F pairCode ![l,v2]]] = _ at ht
  rw [←hp] at ht
  have hb := shortBoundary (⟨3,by decide⟩ : Fin 5) a2 (r+r)
  have hb' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 33,F pairCode ![a2,(r+r)+(r+r)]]) =
      F pairCode ![modelNumeral M 42,F pairCode ![a2+a2,r+r]] := by
    simpa [shortControl,shortExit] using hb
  change F PA194Stepper.stepper ![F addCode ![((c1+c2)+modelNumeral M 3)+modelNumeral M 3,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![(c1+c2)+modelNumeral M 3,modelNumeral M 3],_]) = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![modelNumeral M 3,F PA194Stepper.stepper ![F addCode ![c1+c2,modelNumeral M 3],_]]) = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![modelNumeral M 3,F PA194Stepper.stepper ![modelNumeral M 3,F PA194Stepper.stepper ![F addCode ![c1,c2],_]]]) = _
  rw [PA194StepperCompose.modelStepperCompose,hf,hc,h3,ht,hb']
#print axioms thresholdCycleTo42
end models
end PA194ThresholdCycle
