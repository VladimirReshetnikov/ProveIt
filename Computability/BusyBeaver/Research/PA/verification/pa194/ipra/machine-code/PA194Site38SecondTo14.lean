import PA194Site38SecondTo95
import PA194HalfFileFiveWithTail
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site38SecondTo14
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def lefts (k : M) (args : Fin 11 → M) : Fin 6 → M :=
  let e := physicalArgs args
  let a := F ones ![k,modelNumeral M 6452]
  let b := a+a+1+(a+a+1)+1
  let x1 := F ones ![e 0+1,b+b]
  let x2 := F ones ![e 1+1,x1+x1]
  let x3 := F ones ![e 2+1,x2+x2]
  let x4 := F ones ![e 3+1,x3+x3]
  let x5 := F ones ![e 4+1,x4+x4]
  ![b,x1,x2,x3,x4,x5]
noncomputable def scanCost (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  (((((e 0+1)+1)+((e 1+1)+1))+((e 2+1)+1))+((e 3+1)+1))+((e 4+1)+1)
noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  F addCode ![F addCode ![F addCode ![PA194Site38SecondTo71.firstClock k,modelNumeral M 14],((k+1)+1)+1],scanCost args]
theorem to14 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let p := F ones ![e 5+1,F (fileCode 4) (fun i => e ⟨i.val+6,by omega⟩)]
    let l := lefts k args 5
    F PA194Stepper.stepper ![clock k args,PA194SourceSite31Physical.physicalFrame 38 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 14,F pairCode ![l+l,p]] := by
  dsimp only
  let e := physicalArgs args
  let r := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let a := F ones ![k,modelNumeral M 6452]
  let b := a+a+1+(a+a+1)+1
  have hp : F (fileCode 10) e = r+r := by rw [modelFileSucc,modelBlock]
  have hs := (PA194HalfFileFiveWithTail.scanFiveExact 4 e (b+b) r hp).2
  dsimp only at hs
  change F PA194Stepper.stepper ![scanCost args,F pairCode ![modelNumeral M 95,F pairCode ![b+b,r]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![lefts k args 5+lefts k args 5,
      F ones ![e 5+1,F (fileCode 4) (fun i => e ⟨i.val+6,by omega⟩)]]] at hs
  have h := PA194Site38SecondTo95.to95 k args
  dsimp only at h
  change F PA194Stepper.stepper ![_,_] = F pairCode ![modelNumeral M 95,F pairCode ![b+b,r]] at h
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h,hs]
#print axioms to14
end models
end PA194Site38SecondTo14
