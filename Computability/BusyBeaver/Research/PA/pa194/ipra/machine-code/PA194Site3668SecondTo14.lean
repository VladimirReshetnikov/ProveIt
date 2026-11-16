import PA194Site3668SecondTo71
import PA194HalfFileSixWithTail
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site3668SecondTo14
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def scanCost (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  (((((((e 2+1)+1)+((e 3+1)+1))+((e 4+1)+1))+((e 5+1)+1))+((e 6+1)+1))+((e 7+1)+1))
noncomputable def lefts (k : M) (args : Fin 11 → M) : Fin 9 → M :=
  let e := physicalArgs args
  let b := F ones ![(k+1)+1,modelNumeral M 444]
  let x1 := F ones ![e 0+1,b+b]
  let x2 := F ones ![e 1+1,x1+x1]
  let x3 := F ones ![e 2+1,x2+x2]
  let x4 := F ones ![e 3+1,x3+x3]
  let x5 := F ones ![e 4+1,x4+x4]
  let x6 := F ones ![e 5+1,x5+x5]
  let x7 := F ones ![e 6+1,x6+x6]
  let x8 := F ones ![e 7+1,x7+x7]
  ![b,x1,x2,x3,x4,x5,x6,x7,x8]
noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  let n := (k+1)+1
  let c := ((e 0+1)+1)+((e 1+1)+1)
  F addCode ![F addCode ![F addCode ![F addCode ![PA194Site3668SecondTo60.firstClock k,modelNumeral M 8],n+1],c],scanCost args]

theorem to14 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let p := F ones ![e 8+1,F (fileCode 1) (fun i => e ⟨i.val+9,by omega⟩)]
    let l := lefts k args 8
    F PA194Stepper.stepper ![clock k args,PA194SourceSite31Physical.physicalFrame 3668 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 14,F pairCode ![l+l,p]] := by
  dsimp only
  let e := physicalArgs args
  let e2 : Fin 9 → M := fun i => e i.succ.succ
  let b := F ones ![(k+1)+1,modelNumeral M 444]
  let x1 := F ones ![e 0+1,b+b]
  let x2 := F ones ![e 1+1,x1+x1]
  let p2 := F ones ![e 2+1,F (fileCode 7) (fun i => e i.succ.succ.succ)]
  have hp : F (fileCode 8) e2 = p2+p2 := by rw [modelFileSucc,modelBlock]; rfl
  have hs := (PA194HalfFileSixWithTail.scanSixExact 1 e2 (x2+x2) p2 hp).2
  dsimp only at hs
  change F PA194Stepper.stepper ![scanCost args,F pairCode ![modelNumeral M 71,F pairCode ![x2+x2,p2]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![lefts k args 8+lefts k args 8,
      F ones ![e 8+1,F (fileCode 1) (fun i => e ⟨i.val+9,by omega⟩)]]] at hs
  have h := PA194Site3668SecondTo71.to71 k args
  dsimp only at h
  change _ = F pairCode ![modelNumeral M 71,F pairCode ![x2+x2,p2]] at h
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h,hs]
#print axioms to14
end models
end PA194Site3668SecondTo14
