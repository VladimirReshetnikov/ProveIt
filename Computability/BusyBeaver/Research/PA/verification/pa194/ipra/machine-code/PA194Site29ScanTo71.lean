import PA194Site29SecondDispatch
import PA194GenericRightScan
import PA194UnaryRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ScanTo71
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RightRows PA194UnaryRuns PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem row60one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 60,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 60,F pairCode ![l+l+1,r]] := by
  have h := rightOne 60 1 60 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row60zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 60,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 85,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 60 0 85 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem row85one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 85,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 85,F pairCode ![l+l+1,r]] := by
  have h := rightOne 85 1 85 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row85zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 85,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 106,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 85 0 106 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem row106one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 106,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 106,F pairCode ![l+l+1,r]] := by
  have h := rightOne 106 1 106 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 1 = (1 : M) from modelNumeralOne] using h

theorem row106zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 106,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 71,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 106 0 71 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem threeTo85 (l p : M) :
    let a := p+p
    let b := a+a+1
    let c := b+b+1
    let l1 := l+l+1
    let l2 := l1+l1+1
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 60,F pairCode ![l,c]]] =
    F pairCode ![modelNumeral M 85,F pairCode ![l2+l2,p]] := by
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,row60one,row60one,row60zero]

theorem scanTo71 (k n m l r : M) :
    let b := F ones ![m+1,r+r]
    let p := F ones ![n+1,b+b]
    let a := p+p
    let c := a+a+1
    let tail := c+c+1
    let l0 := F ones ![k,l]
    let l1 := l0+l0+1
    let l2 := l1+l1+1
    let l3 := l2+l2
    let l4 := F ones ![n+1,l3]
    let l5 := l4+l4
    let l6 := F ones ![m+1,l5]
    F PA194Stepper.stepper ![((k+modelNumeral M 3)+((n+1)+1))+((m+1)+1),
      F pairCode ![modelNumeral M 60,F pairCode ![l,F ones ![k,tail]]]] =
    F pairCode ![modelNumeral M 71,F pairCode ![l6+l6,r]] := by
  dsimp only
  let b := F ones ![m+1,r+r]
  let p := F ones ![n+1,b+b]
  let a := p+p
  let c := a+a+1
  let tail := c+c+1
  let l0 := F ones ![k,l]
  let l1 := l0+l0+1
  let l2 := l1+l1+1
  let l3 := l2+l2
  let l4 := F ones ![n+1,l3]
  let l5 := l4+l4
  let l6 := F ones ![m+1,l5]
  have h60 := PA194GenericRightScan.modelFullScan 60 (row60one (M := M)) k l tail
  have h3 := threeTo85 (M := M) l0 p
  dsimp only at h3
  have h85 := PA194GenericRightScan.modelFullScan 85 (row85one (M := M)) (n+1) l3 (b+b)
  have h85exit := row85zero (M := M) l4 b
  have h106 := PA194GenericRightScan.modelFullScan 106 (row106one (M := M)) (m+1) l5 (r+r)
  have h106exit := row106zero (M := M) l6 r
  change F PA194Stepper.stepper ![F addCode ![(k+modelNumeral M 3)+((n+1)+1),(m+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![(m+1)+1,F PA194Stepper.stepper ![F addCode ![k+modelNumeral M 3,(n+1)+1],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![(m+1)+1,F PA194Stepper.stepper ![(n+1)+1,F PA194Stepper.stepper ![F addCode ![k,modelNumeral M 3],_]]] = _
  rw [PA194StepperCompose.modelStepperCompose,h60,h3]
  change F PA194Stepper.stepper ![(m+1)+1,F PA194Stepper.stepper ![F addCode ![n+1,F oneCode Fin.elim0],_]] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,h85,h85exit]
  change F PA194Stepper.stepper ![F addCode ![m+1,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc,h106,h106exit]
#print axioms scanTo71
end models
end PA194Site29ScanTo71
