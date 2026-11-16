import PA194HalfFileTwoWithTail
import PA194SixteenTwoRuns
import PA194FourteenOddTo16
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194NinetyThreeReturnTwoWithTail
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194HalfFileTwoWithTail PA194SixteenTwoRuns PA194FourteenOddTo16
open PA194RegisterFile PA194UnaryRuns PA194BinaryDouble BinaryTapeCodes
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

theorem ninetyThreeReturnTwoWithTail (n : Nat) (e : Fin (n+4) → M) (l p : M)
    (hp : F (fileCode (n+3)) e = p+p) :
    ∃ time w : M, F PA194Stepper.stepper ![time,F pairCode ![modelNumeral M 93,F pairCode ![l+l,p]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let x := F ones ![e ⟨0,by omega⟩+1,l+l]
  let a := F ones ![e ⟨1,by omega⟩,x+x]
  let last : Fin (n+2) → M := fun i => e ⟨i.val+2,by omega⟩
  let suffix := F (fileCode n) (fun i => last i.succ)
  let b := F ones ![last 0,suffix]
  let c := (b+b)+(b+b)
  let w1 := F ones ![e ⟨1,by omega⟩,(1 : M)+c+c]
  let w2 := F ones ![e ⟨0,by omega⟩,(1 : M)+(w1+w1)+(w1+w1)]
  let back := (e ⟨1,by omega⟩+1)+((e ⟨0,by omega⟩+1)+1)
  obtain ⟨t,right,hfile,hscan⟩ := scanTwoWithTail n e (l+l) p hp
  have hsucc : F ones ![last 0+1,suffix] = b+b+1 := by
    change F ones ![F addCode ![last 0,F oneCode Fin.elim0],suffix] = _
    rw [modelAddOne,modelOnesSucc]
  have hf : F (fileCode (n+1)) last = (b+b+1)+(b+b+1) := by
    rw [modelFileSucc,modelBlock,hsucc]
  change F (fileCode (n+1)) last = right+right at hfile
  have hh := congrArg (fun z : M => F halfCode (fun _ => z)) (hf.symm.trans hfile)
  rw [(modelDouble (b+b+1)).2,(modelDouble right).2] at hh
  have hright : right=b+b+1 := hh.symm
  rw [hright] at hscan
  have h16 := fourteenOddTo16 a b
  have h17 := modelSixteenTwoRuns (e ⟨1,by omega⟩) (e ⟨0,by omega⟩) l c
  dsimp only at hscan h16 h17
  refine ⟨(t+modelNumeral M 3)+back,w2,?_⟩
  change F PA194Stepper.stepper ![F addCode ![t+modelNumeral M 3,back],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![back,F PA194Stepper.stepper ![F addCode ![t,modelNumeral M 3],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hscan,h16]
  exact h17

/-- Exact state-93 two-block return with the complete residual suffix and
model-valued running time retained. -/
theorem ninetyThreeReturnTwoWithTailExact (n : Nat) (e : Fin (n+4) → M) (l p : M)
    (hp : F (fileCode (n+3)) e = p+p) :
    let e1 : Fin (n+3) → M := fun i => e i.succ
    let e2 : Fin (n+2) → M := fun i => e1 i.succ
    let b := F ones ![e2 0,F (fileCode n) (fun i => e2 i.succ)]
    let c := (b+b)+(b+b)
    let w1 := F ones ![e1 0,(1 : M)+c+c]
    let w2 := F ones ![e 0,(1 : M)+(w1+w1)+(w1+w1)]
    let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
    let backClock := (e1 0+1)+((e 0+1)+1)
    F PA194Stepper.stepper ![(scanClock+modelNumeral M 3)+backClock,
      F pairCode ![modelNumeral M 93,F pairCode ![l+l,p]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w2+w2)+(w2+w2)]] := by
  dsimp only
  let e1 : Fin (n+3) → M := fun i => e i.succ
  let e2 : Fin (n+2) → M := fun i => e1 i.succ
  let x := F ones ![e 0+1,l+l]
  let a := F ones ![e1 0,x+x]
  let b := F ones ![e2 0,F (fileCode n) (fun i => e2 i.succ)]
  let c := (b+b)+(b+b)
  let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
  let backClock := (e1 0+1)+((e 0+1)+1)
  have hscan := scanTwoWithTailExact n e (l+l) p hp
  dsimp only at hscan
  have h16 := fourteenOddTo16 a b
  have h17 := modelSixteenTwoRuns (e1 0) (e 0) l c
  dsimp only at h16 h17
  change F PA194Stepper.stepper ![F addCode ![scanClock+modelNumeral M 3,backClock],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![backClock,F PA194Stepper.stepper ![F addCode ![scanClock,modelNumeral M 3],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hscan,h16]
  exact h17
#print axioms ninetyThreeReturnTwoWithTailExact
#print axioms ninetyThreeReturnTwoWithTail
end models
end PA194NinetyThreeReturnTwoWithTail
