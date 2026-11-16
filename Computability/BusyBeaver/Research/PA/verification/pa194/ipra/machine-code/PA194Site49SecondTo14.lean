import PA194Site49SecondTo93
import PA194HalfFileWithTail
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site49SecondTo14
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
    let a := F ones ![k,modelNumeral M 848]
    let l := a+a+1+(a+a+1)+1
    let x1 := F ones ![e 0+1,l+l]
    let x2 := F ones ![e 1+1,x1+x1]
    let x3 := F ones ![e 2+1,x2+x2]
    let x4 := F ones ![e 3+1,x3+x3]
    let p4 := F ones ![e 4+1,F (fileCode 5) (fun i => e ⟨i.val+5,by omega⟩)]
    let c := ((e 0+1)+1)+((e 1+1)+1)
    let d := ((e 2+1)+1)+((e 3+1)+1)
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![F addCode ![PA194Site49SecondTo95.firstClock k,modelNumeral M 11],n+1],c],d],
      PA194SourceSite31Physical.physicalFrame 49 n args] =
      F pairCode ![modelNumeral M 14,F pairCode ![x4+x4,p4]] := by
  dsimp only
  let n := (k+1)+1
  let e := physicalArgs args
  let e2 : Fin 9 → M := fun i => e i.succ.succ
  let e3 : Fin 8 → M := fun i => e i.succ.succ.succ
  let a := F ones ![k,modelNumeral M 848]
  let l := a+a+1+(a+a+1)+1
  let x1 := F ones ![e 0+1,l+l]
  let x2 := F ones ![e 1+1,x1+x1]
  let x3 := F ones ![e 2+1,x2+x2]
  let x4 := F ones ![e 3+1,x3+x3]
  let p2 := F ones ![e2 0+1,F (fileCode 7) (fun i => e2 i.succ)]
  let p3 := F ones ![e3 0+1,F (fileCode 6) (fun i => e3 i.succ)]
  have hp : F (fileCode 8) e2 = p2+p2 := by rw [modelFileSucc,modelBlock]
  have loop93 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 93,F pairCode ![x+x+1,y]] := by
    have h := rightOne 93 1 93 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit93 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 93,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 113,F pairCode ![x+x,y]] := by
    have h := rightZero 93 0 113 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have loop113 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 113,F pairCode ![x+x+1,y]] := by
    have h := rightOne 113 1 113 (by decide) (by decide +kernel) x y
    simpa only [modelNumeralOne] using h
  have exit113 (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 14,F pairCode ![x+x,y]] := by
    have h := rightZero 113 0 14 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have h1 := scanHalfBlockWithTailExact 6 93 113 e2 (x2+x2) p2 hp loop93 exit93
  dsimp only at h1
  have he2 : e2 0 = e 2 := congrArg e (by decide)
  rw [he2] at h1
  have h2 := scanHalfBlockWithTailExact 5 113 14 e3 (x3+x3) p3 h1.1 loop113 exit113
  dsimp only at h2
  have start := PA194Site49SecondTo93.to93 k args
  dsimp only at start
  change F PA194Stepper.stepper ![_,_] = F pairCode ![modelNumeral M 93,F pairCode ![x2+x2,p2]] at start
  have h2' := h2.2
  change F PA194Stepper.stepper ![(e 3+1)+1,F pairCode ![modelNumeral M 113,F pairCode ![x3+x3,p3]]] =
    F pairCode ![modelNumeral M 14,F pairCode ![x4+x4,F ones ![e 4+1,F (fileCode 5) (fun i => e ⟨i.val+5,by omega⟩)]]] at h2'
  change F PA194Stepper.stepper ![F addCode ![_,F addCode ![(e 2+1)+1,(e 3+1)+1]],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![F addCode ![(e 2+1)+1,(e 3+1)+1],F PA194Stepper.stepper ![_,_]] = _
  rw [PA194StepperCompose.modelStepperCompose,start,h1.2,h2']
#print axioms to14
end models
end PA194Site49SecondTo14
