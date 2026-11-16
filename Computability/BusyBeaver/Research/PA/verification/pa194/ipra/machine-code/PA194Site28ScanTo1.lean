import PA194StepperCompose
import PA194TwoScanInvariant
import PA194OnesCommute
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28ScanTo1
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194OnesCommute PA194UnaryRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem row2one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 2,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 2,F pairCode ![l+l+1,r]] := by
  have h := rightOne 2 1 2 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row2zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 2,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 0,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 2 0 0 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem row0one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 0,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 2,F pairCode ![l+l+1,r]] := by
  have h := rightOne 0 1 2 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row0zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 0,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 1,F pairCode ![l+l+1,r]] := by
  have h := rightZero 0 1 1 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem firstTwo (l w : M) :
    let w1 := w+w
    let x := (w1+w1)+1
    let a := l+l+1
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 2,F pairCode ![l,x]]] =
    F pairCode ![modelNumeral M 0,F pairCode ![a+a,w]] := by
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,row2one,row2zero]
  rfl

theorem lastTwo (l b : M) :
    let c := b+b
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 2,F pairCode ![l,c+c]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(l+l)+(l+l)+1,b]] := by
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,row2zero,row0zero]
  rfl

theorem scanTo1 (k v l b : M) :
    let c := b+b
    let w := F ones ![v,(1 : M)+(c+c)+(c+c)]
    let a := F ones ![k,l]
    let a1 := a+a+1
    let a2 := a1+a1
    let a3 := a2+a2+1
    let a4 := F ones ![v,a3]
    F PA194Stepper.stepper ![((k+modelNumeral M 2)+(modelNumeral M 1+v))+modelNumeral M 2,
      F pairCode ![modelNumeral M 2,F pairCode ![l,F ones ![k,(1 : M)+(w+w)+(w+w)]]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(a4+a4)+(a4+a4)+1,b]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let c := b+b
  let w := F ones ![v,(1 : M)+(c+c)+(c+c)]
  let a := F ones ![k,l]
  let a1 := a+a+1
  let a2 := a1+a1
  let a3 := a2+a2+1
  let a4 := F ones ![v,a3]
  let tail := F ones ![v,c+c]
  have hk := PA194TwoScanInvariant.modelFullScan k l ((1 : M)+(w+w)+(w+w))
  have h2 := firstTwo (M := M) a w
  dsimp only at h2
  have hs : (1 : M)+(w+w)+(w+w) = (w+w)+(w+w)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hs] at hk
  have hword : w=tail+tail+1 := by
    dsimp only [w,tail]
    have hw : (1 : M)+(c+c)+(c+c) = (c+c)+(c+c)+1 := by simp only [add_assoc,add_comm,add_left_comm]
    rw [hw,modelOnesCommute]
  have h0 := row0one (M := M) a2 tail
  rw [←hword] at h0
  change F PackedClock.encodedStep (fun _ => F pairCode ![F (Code.zero 0) Fin.elim0,F pairCode ![a1+a1,w]]) =
    F pairCode ![modelNumeral M 2,F pairCode ![a3,tail]] at h0
  have hv := PA194TwoScanInvariant.modelFullScan v a3 (c+c)
  have hl := lastTwo (M := M) a4 b
  dsimp only at hl
  change F PA194Stepper.stepper ![((k+modelNumeral M 2)+(modelNumeral M 1+v))+modelNumeral M 2,
    F pairCode ![modelNumeral M 2,F pairCode ![l,F ones ![k,(1 : M)+(w+w)+(w+w)]]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(a4+a4)+(a4+a4)+1,b]]
  rw [hs]
  change F PA194Stepper.stepper ![F addCode ![(k+modelNumeral M 2)+(modelNumeral M 1+v),modelNumeral M 2],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 2,F PA194Stepper.stepper ![F addCode ![k+modelNumeral M 2,modelNumeral M 1+v],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 2,F PA194Stepper.stepper ![F addCode ![modelNumeral M 1,v],F PA194Stepper.stepper ![F addCode ![k,modelNumeral M 2],_]]] = _
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hk,h2]
  change F PA194Stepper.stepper ![modelNumeral M 2,F PA194Stepper.stepper ![v,F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_]]] = _
  rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,h0,hv,hl]
#print axioms scanTo1
end models
end PA194Site28ScanTo1
