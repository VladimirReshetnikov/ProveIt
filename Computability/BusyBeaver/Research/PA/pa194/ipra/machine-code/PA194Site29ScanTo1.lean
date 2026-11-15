import PA194Site29TwoFile
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ScanTo1
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterFile PA194UnaryRuns PA194OnesCommute PA194Site28ScanTo1 PA194Site29TwoFile PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem scanTo1 (k v0 v1 l q : M) (e : Fin 7 → M)
    (he : e 6 = (q+q)+(q+q)) :
    let file := F (fileCode 6) e
    let w1 := F ones ![v1,(1 : M)+file+file]
    let w0 := F ones ![v0,(1 : M)+(w1+w1)+(w1+w1)]
    let a := F ones ![k,l]
    let a1 := a+a+1
    let a2 := a1+a1
    let a3 := a2+a2+1
    let z := F ones ![v0,a3]
    let b := (z+z)+(z+z)+1
    let left := finalLeft 6 v1 b e
    let count := finalCount 6 v1 e
    let x := F ones ![count,left]
    let clock := (((((k+modelNumeral M 2)+modelNumeral M 1)+(v0+modelNumeral M 2))+
      fileClock 6 v1 e)+count)+modelNumeral M 2
    F PA194Stepper.stepper ![clock,F pairCode ![modelNumeral M 2,
      F pairCode ![l,F ones ![k,(1 : M)+(w0+w0)+(w0+w0)]]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(x+x)+(x+x)+1,q]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let file := F (fileCode 6) e
  let w1 := F ones ![v1,(1 : M)+file+file]
  let w0 := F ones ![v0,(1 : M)+(w1+w1)+(w1+w1)]
  let a := F ones ![k,l]
  let a1 := a+a+1
  let a2 := a1+a1
  let a3 := a2+a2+1
  let z := F ones ![v0,a3]
  let b := (z+z)+(z+z)+1
  let left := finalLeft 6 v1 b e
  let count := finalCount 6 v1 e
  let x := F ones ![count,left]
  let middle := F ones ![v0,w1+w1]
  have hword : w0 = middle+middle+1 := by
    dsimp only [w0,middle]
    have h : (1 : M)+(w1+w1)+(w1+w1) = (w1+w1)+(w1+w1)+1 := by
      simp only [add_assoc,add_comm,add_left_comm]
    rw [h,modelOnesCommute]
  have hk := PA194TwoScanInvariant.modelFullScan k l ((1 : M)+(w0+w0)+(w0+w0))
  have h2 := firstTwo (M := M) a w0
  dsimp only at h2
  have hs : (1 : M)+(w0+w0)+(w0+w0) = (w0+w0)+(w0+w0)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hs] at hk
  have h0 := row0one (M := M) a2 middle
  rw [←hword] at h0
  change F PackedClock.encodedStep (fun _ => F pairCode ![F (Code.zero 0) Fin.elim0,F pairCode ![a2,w0]]) = _ at h0
  have hop := PA194Site29TwoBlock.traverse v0 a3 v1 file
  dsimp only at hop
  have hf := traverseFile 6 v1 b e
  change F PA194Stepper.stepper ![fileClock 6 v1 e,F pairCode ![modelNumeral M 2,F pairCode ![b,F ones ![v1,file]]]] = F pairCode ![modelNumeral M 2,F pairCode ![left,F ones ![count,e 6]]] at hf
  rw [he] at hf
  have hlast := PA194TwoScanInvariant.modelFullScan count left ((q+q)+(q+q))
  have hend := lastTwo (M := M) x q
  dsimp only at hend
  rw [hs]
  change F PA194Stepper.stepper ![F addCode ![(((((k+modelNumeral M 2)+modelNumeral M 1)+(v0+modelNumeral M 2))+fileClock 6 v1 e)+count),modelNumeral M 2],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![(((k+modelNumeral M 2)+modelNumeral M 1)+(v0+modelNumeral M 2))+fileClock 6 v1 e,count],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![((k+modelNumeral M 2)+modelNumeral M 1)+(v0+modelNumeral M 2),fileClock 6 v1 e],_]]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![(k+modelNumeral M 2)+modelNumeral M 1,v0+modelNumeral M 2],_]]]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![k+modelNumeral M 2,modelNumeral M 1],_]]]]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F addCode ![k,modelNumeral M 2],_]]]]]] = _
  rw [PA194StepperCompose.modelStepperCompose,hk,h2]
  change F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![_,F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_]]]]] = _
  rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,h0]
  rw [hop,hf,hlast,hend]
#print axioms scanTo1
end models
end PA194Site29ScanTo1
