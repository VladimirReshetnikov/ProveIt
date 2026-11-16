import PA194Site3664SecondTo106
import PA194HalfFileWithTail
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3664SecondTo14
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

theorem to14 (k : M) (args : Fin 11 → M) :
    let n := (k+1)+1
    let e := physicalArgs args
    let a := F ones ![k,modelNumeral M 440]
    let l := a+a+1+(a+a+1)+1
    let x1 := F ones ![e 0+1,l+l]
    let x2 := F ones ![e 1+1,x1+x1]
    let x3 := F ones ![e 2+1,x2+x2]
    let x4 := F ones ![e 3+1,x3+x3]
    let x5 := F ones ![e 4+1,x4+x4]
    let x6 := F ones ![e 5+1,x5+x5]
    let x7 := F ones ![e 6+1,x6+x6]
    let p7 := F ones ![e 7+1,F (fileCode 2) (fun i => e ⟨i.val+8,by omega⟩)]
    let c := F addCode ![F addCode ![F addCode ![F addCode ![F addCode ![F addCode ![(e 0+1)+1,(e 1+1)+1],(e 2+1)+1],(e 3+1)+1],(e 4+1)+1],(e 5+1)+1],(e 6+1)+1]
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![PA194Site3664SecondTo85.firstClock k,modelNumeral M 8],n+1],c],
      PA194SourceSite31Physical.physicalFrame 3664 n args] =
      F pairCode ![modelNumeral M 14,F pairCode ![x7+x7,p7]] := by
  dsimp only
  let e := physicalArgs args
  let e1 : Fin 10 → M := fun i => e i.succ
  let e2 : Fin 9 → M := fun i => e1 i.succ
  let e3 : Fin 8 → M := fun i => e2 i.succ
  let e4 : Fin 7 → M := fun i => e3 i.succ
  let e5 : Fin 6 → M := fun i => e4 i.succ
  let e6 : Fin 5 → M := fun i => e5 i.succ
  let a := F ones ![k,modelNumeral M 440]
  let l := a+a+1+(a+a+1)+1
  let x1 := F ones ![e 0+1,l+l]
  let x2 := F ones ![e 1+1,x1+x1]
  let x3 := F ones ![e 2+1,x2+x2]
  let x4 := F ones ![e 3+1,x3+x3]
  let x5 := F ones ![e 4+1,x4+x4]
  let x6 := F ones ![e 5+1,x5+x5]
  let x7 := F ones ![e 6+1,x6+x6]
  let p0 := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let p1 := F ones ![e1 0+1,F (fileCode 8) (fun i => e1 i.succ)]
  let p2 := F ones ![e2 0+1,F (fileCode 7) (fun i => e2 i.succ)]
  let p3 := F ones ![e3 0+1,F (fileCode 6) (fun i => e3 i.succ)]
  let p4 := F ones ![e4 0+1,F (fileCode 5) (fun i => e4 i.succ)]
  let p5 := F ones ![e5 0+1,F (fileCode 4) (fun i => e5 i.succ)]
  let p6 := F ones ![e6 0+1,F (fileCode 3) (fun i => e6 i.succ)]
  have hp : F (fileCode 10) e = p0+p0 := by rw [modelFileSucc,modelBlock]
  have loop0 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 106,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 106,F pairCode ![x+x+1,y]] := by
    have h := rightOne 106 1 106 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit0 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 106,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 71,F pairCode ![x+x,y]] := by
    have h := rightZero 106 0 71 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have loop1 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 71,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 71,F pairCode ![x+x+1,y]] := by
    have h := rightOne 71 1 71 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit1 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 71,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 95,F pairCode ![x+x,y]] := by
    have h := rightZero 71 0 95 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have loop2 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 95,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 95,F pairCode ![x+x+1,y]] := by
    have h := rightOne 95 1 95 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit2 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 95,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 114,F pairCode ![x+x,y]] := by
    have h := rightZero 95 0 114 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have loop3 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 114,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 114,F pairCode ![x+x+1,y]] := by
    have h := rightOne 114 1 114 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit3 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 114,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 68,F pairCode ![x+x,y]] := by
    have h := rightZero 114 0 68 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have loop4 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 68,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 68,F pairCode ![x+x+1,y]] := by
    have h := rightOne 68 1 68 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit4 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 68,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 93,F pairCode ![x+x,y]] := by
    have h := rightZero 68 0 93 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have loop5 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 93,F pairCode ![x+x+1,y]] := by
    have h := rightOne 93 1 93 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit5 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 113,F pairCode ![x+x,y]] := by
    have h := rightZero 93 0 113 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have loop6 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 113,F pairCode ![x+x+1,y]] := by
    have h := rightOne 113 1 113 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit6 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 14,F pairCode ![x+x,y]] := by
    have h := rightZero 113 0 14 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have h1 := scanHalfBlockWithTailExact 8 106 71 e (l+l) p0 hp loop0 exit0
  dsimp only at h1
  have h2 := scanHalfBlockWithTailExact 7 71 95 e1 (x1+x1) p1 h1.1 loop1 exit1
  dsimp only at h2
  have h3 := scanHalfBlockWithTailExact 6 95 114 e2 (x2+x2) p2 h2.1 loop2 exit2
  dsimp only at h3
  have h4 := scanHalfBlockWithTailExact 5 114 68 e3 (x3+x3) p3 h3.1 loop3 exit3
  dsimp only at h4
  have h5 := scanHalfBlockWithTailExact 4 68 93 e4 (x4+x4) p4 h4.1 loop4 exit4
  dsimp only at h5
  have h6 := scanHalfBlockWithTailExact 3 93 113 e5 (x5+x5) p5 h5.1 loop5 exit5
  dsimp only at h6
  have h7 := scanHalfBlockWithTailExact 2 113 14 e6 (x6+x6) p6 h6.1 loop6 exit6
  dsimp only at h7
  have start := PA194Site3664SecondTo106.to106 k args
  dsimp only at start
  change F PA194Stepper.stepper ![_,_] = F pairCode ![modelNumeral M 106,F pairCode ![l+l,p0]] at start
  have hh1 := h1.2
  change F PA194Stepper.stepper ![(e 0+1)+1,F pairCode ![modelNumeral M 106,F pairCode ![l+l,p0]]] =
    F pairCode ![modelNumeral M 71,F pairCode ![x1+x1,p1]] at hh1
  have hh2 := h2.2
  change F PA194Stepper.stepper ![(e 1+1)+1,F pairCode ![modelNumeral M 71,F pairCode ![x1+x1,p1]]] =
    F pairCode ![modelNumeral M 95,F pairCode ![x2+x2,p2]] at hh2
  have hh3 := h3.2
  change F PA194Stepper.stepper ![(e 2+1)+1,F pairCode ![modelNumeral M 95,F pairCode ![x2+x2,p2]]] =
    F pairCode ![modelNumeral M 114,F pairCode ![x3+x3,p3]] at hh3
  have hh4 := h4.2
  change F PA194Stepper.stepper ![(e 3+1)+1,F pairCode ![modelNumeral M 114,F pairCode ![x3+x3,p3]]] =
    F pairCode ![modelNumeral M 68,F pairCode ![x4+x4,p4]] at hh4
  have hh5 := h5.2
  change F PA194Stepper.stepper ![(e 4+1)+1,F pairCode ![modelNumeral M 68,F pairCode ![x4+x4,p4]]] =
    F pairCode ![modelNumeral M 93,F pairCode ![x5+x5,p5]] at hh5
  have hh6 := h6.2
  change F PA194Stepper.stepper ![(e 5+1)+1,F pairCode ![modelNumeral M 93,F pairCode ![x5+x5,p5]]] =
    F pairCode ![modelNumeral M 113,F pairCode ![x6+x6,p6]] at hh6
  have hh7 := h7.2
  change F PA194Stepper.stepper ![(e 6+1)+1,F pairCode ![modelNumeral M 113,F pairCode ![x6+x6,p6]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![x7+x7,F ones ![e 7+1,F (fileCode 2) (fun i => e ⟨i.val+8,by omega⟩)]]] at hh7
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,start,hh1,hh2,hh3,hh4,hh5,hh6,hh7]
#print axioms to14
end models
end PA194Site3664SecondTo14
