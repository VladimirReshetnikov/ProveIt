import PA194Site48SecondTo114
import PA194HalfFileWithTail
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site48SecondTo93
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile PA194HalfFileWithTail BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194RightRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem to93 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let e := physicalArgs args
    let a := F ones ![k,modelNumeral M 104]
    let l := a+a+1+(a+a+1)+1
    let x1 := F ones ![e 0+1,l+l]
    let x2 := F ones ![e 1+1,x1+x1]
    let p2 := F ones ![e 2+1,F (fileCode 7) (fun i => e i.succ.succ.succ)]
    let c := ((e 0+1)+1)+((e 1+1)+1)
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![PA194Site48SecondTo95.firstClock k,modelNumeral M 8],n+1],c],
      PA194SourceSite31Physical.physicalFrame 48 n args] =
      F pairCode ![modelNumeral M 93,F pairCode ![x2+x2,p2]] := by
  dsimp only
  let n := (k+1)+1
  let e := physicalArgs args
  let e1 : Fin 10 → M := fun i => e i.succ
  let a := F ones ![k,modelNumeral M 104]
  let l := a+a+1+(a+a+1)+1
  let x1 := F ones ![e 0+1,l+l]
  let x2 := F ones ![e 1+1,x1+x1]
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let p1 := F ones ![e1 0+1,F (fileCode 8) (fun i => e1 i.succ)]
  have hp : F (fileCode 10) e = p+p := by rw [modelFileSucc,modelBlock]
  have loop114 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 114,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 114,F pairCode ![x+x+1,y]] := by
    have h := rightOne 114 1 114 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit114 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 114,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 68,F pairCode ![x+x,y]] := by
    have h := rightZero 114 0 68 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have loop68 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 68,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 68,F pairCode ![x+x+1,y]] := by
    have h := rightOne 68 1 68 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit68 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 68,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 93,F pairCode ![x+x,y]] := by
    have h := rightZero 68 0 93 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have h1 := scanHalfBlockWithTailExact 8 114 68 e (l+l) p hp loop114 exit114
  dsimp only at h1
  have h2 := scanHalfBlockWithTailExact 7 68 93 e1 (x1+x1) p1 h1.1 loop68 exit68
  dsimp only at h2
  have start := PA194Site48SecondTo114.to114 k args
  dsimp only at start
  change F PA194Stepper.stepper ![_,_] = F pairCode ![modelNumeral M 114,F pairCode ![l+l,p]] at start
  have h2' := h2.2
  change F PA194Stepper.stepper ![(e 1+1)+1,F pairCode ![modelNumeral M 68,F pairCode ![x1+x1,p1]]] =
    F pairCode ![modelNumeral M 93,F pairCode ![x2+x2,F ones ![e 2+1,F (fileCode 7) (fun i => e i.succ.succ.succ)]]] at h2'
  change F PA194Stepper.stepper ![F addCode ![F addCode ![_,_],F addCode ![(e 0+1)+1,(e 1+1)+1]],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![F addCode ![(e 0+1)+1,(e 1+1)+1],F PA194Stepper.stepper ![_,_]] = _
  rw [PA194StepperCompose.modelStepperCompose,start,h1.2,h2']
#print axioms to93
end models
end PA194Site48SecondTo93
