import PA194HalfFileWithTail
import PA194Site43SecondTo113
import PA194Site43GapScan
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site43SecondTo14
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

theorem to14 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let a := F ones ![k,modelNumeral M 812]
    let b := a+a+1+(a+a+1)+1
    let x := F ones ![e 0+1,b+b]
    let p := F ones ![e 1+1,F (fileCode 8) (fun i => e i.succ.succ)]
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![PA194Site43SecondTo93.firstClock k,modelNumeral M 9],((k+1)+1)+1],(e 0+1)+1],
      PA194SourceSite31Physical.physicalFrame 43 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 14,F pairCode ![x+x,p]] := by
  dsimp only
  let e := physicalArgs args
  let r := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let a := F ones ![k,modelNumeral M 812]
  let b := a+a+1+(a+a+1)+1
  have hp : F (fileCode 10) e = r+r := by rw [modelFileSucc,modelBlock]
  have hloop (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y+1]]) = F pairCode ![modelNumeral M 113,F pairCode ![x+x+1,y]] := by
    have h := PA194RightRows.rightOne 113 1 113 (by decide) (by decide +kernel) x y
    simpa only [PA194StateOne.modelNumeralOne] using h
  have hexit (x y : M) : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![x,y+y]]) = F pairCode ![modelNumeral M 14,F pairCode ![x+x,y]] := by
    have h := PA194RightRows.rightZero 113 0 14 (by decide) (by decide +kernel) x y
    simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h
  have hs := (PA194HalfFileWithTail.scanHalfBlockWithTailExact 8 113 14 e (b+b) r hp hloop hexit).2
  dsimp only at hs
  have h := PA194Site43SecondTo113.to113 k args
  dsimp only at h
  change F PA194Stepper.stepper ![_,_] = F pairCode ![modelNumeral M 113,F pairCode ![b+b,r]] at h
  rw [PA194StepperCompose.modelStepperCompose,h,hs]
  have hi : (Fin.succ (0 : Fin 10) : Fin 11) = 1 := by decide
  rw [hi]
#print axioms to14
end models
end PA194Site43SecondTo14
