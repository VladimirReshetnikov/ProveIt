import PA194ZeroFirstContinue
import PA194ContinueTwoHeader
import PA194ContinueIncrementTo24
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroIncrementContinue
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ZeroFirstContinue PA194ContinueTwoHeader PA194ContinueIncrementTo24 PA194IncrementOutputEven PA194SevenToRootControl PA194IncrementOutputExact PA194ReturnFile PA194ReturnFileMeaning PA194MarkedFile PA194CarryFile PA194SevenIncrementHeader PA194SeventeenToRootControl PA194IncrementHeaderReturn PA194SevenToSixteen PA194RegisterFile PA194ZeroRuns
open BinaryTapeCodes PA194UnaryRuns PA194SixteenScanExit PA194BinaryDouble
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
/-- Continue any checked increment output with a positive first block. -/
theorem zeroIncrementToContinueTarget (u : M) (file : Fin 8 → M) (next spare clock start : M)
    (hrun :
      let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
      let h := g+g+1
      let xx := h+h+1
      let ll := (xx+xx)+(xx+xx)+1
      let a0 := ll+ll+1
      let a1 := a0+a0+1
      let a2 := a1+a1+1
      let a3 := a2+a2+1
      let args : Fin 3 → M := ![next,spare,(0 : M)]
      let ep := replaceLast 7 file (F (markedFile 1) args)
      let c3 := ((1 : M)+1)+1
      let six := c3+c3
      let rest := F (fileCode 1) (replaceLast 1 (fun i => args i.succ) six)
      let result := F block ![next+1,rest]
      let out := F (returnCode 7) (Fin.cases result ep)
      let b := F block ![(0 : M),out]
      F PA194Stepper.stepper ![clock,start] =
        F pairCode ![modelNumeral M 7,F pairCode ![a3+a3,b+b]]) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let args : Fin 3 → M := ![next,spare,(0 : M)]
    let ep := replaceLast 7 file (F (markedFile 1) args)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let rest := F (fileCode 1) (replaceLast 1 (fun i => args i.succ) six)
    let result := F block ![next+1,rest]
    let out := F (returnCode 7) (Fin.cases result ep)
    ∃ r : M, out = r+r ∧
      let t := (1 : M)+(r+r)+(r+r)
      let z := t+t
      let rr := z+z
      let tt := (rr+rr)+(rr+rr)
      let w := F ones ![modelNumeral M 3,1+tt+tt]
      let c := (modelNumeral M 2+(((modelNumeral M 2+1)+(0 : M))+1+1))+modelNumeral M 2
      let ct := (((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
      F PA194Stepper.stepper ![clock+(((c+((modelNumeral M 5+1)+1))+ct)+modelNumeral M 32),start] =
        F pairCode ![modelNumeral M 24,F pairCode ![h,1+(w+w)+(w+w)]] := by
  dsimp only at hrun ⊢
  obtain ⟨r,hr⟩ := outputEven file next spare
  refine ⟨r,hr,?_⟩
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hrun,hr]
  exact zeroToContinueTarget u r
#print axioms zeroIncrementToContinueTarget
end models
end PA194ZeroIncrementContinue
