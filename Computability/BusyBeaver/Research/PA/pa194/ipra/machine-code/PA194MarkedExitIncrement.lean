import PA194MarkedExitTo2
import PA194MarkedIncrementHead
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194MarkedExitIncrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194RegisterFile PA194MarkedFile PA194CarryFile PA194ReturnFile PA194ReturnFileMeaning
open PA194MarkedExitTo2 PA194MarkedIncrementHead PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- The marked-slot-8 exit reaches and executes the increment box, given the
explicit one-spare and blank-suffix layout. -/
theorem markedExitIncrement (u k : M) (ep : Fin 8 → M) (e : Fin 3 → M)
    (hp : ep (Fin.last 7) = F (markedFile 1) e)
    (he : e (Fin.last 2) = (0 : M)) :
    let f := F (fileCode 7) ep
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let l := F ones ![k,(a3+a3)+(a3+a3)]
    let c1 := ((((k+1)+1)+1)+1)+1+((modelNumeral M 3+1)+1)
    let c2 := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let dispatch := (c1+(((c2+modelNumeral M 3)+modelNumeral M 4)+1))+modelNumeral M 10
    let prefixCost := F (costCode 7) ep
    let front := (((1 : M)+1)+e 0)+F (costCode 1) (fun i => e i.succ)
    let incrementCost := ((front+modelNumeral M 6)+F (costCode 1) (fun i => e i.succ))+((e 0+1)+1+1)
    let c3 := ((1 : M)+1)+1
    let six := c3+c3
    let rest := F (fileCode 1) (replaceLast 1 (fun i => e i.succ) six)
    let result := F block ![e 0+1,rest]
    let out := F (returnCode 7) (Fin.cases result ep)
    let clock := (prefixCost+incrementCost)+prefixCost
    F PA194Stepper.stepper ![dispatch+(((k+1)+clock)+((k+1)+1)),
      F pairCode ![modelNumeral M 17,F pairCode ![l+l+1,(1 : M)+f+f]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![a3+a3,F block ![k,out]+F block ![k,out]]] := by
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2+1
  have hd := markedTo2 u k (F (fileCode 7) ep)
  dsimp only at hd
  have hi := incrementAfterHead k (a3+a3) ep e hp he
  dsimp only at hi
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hd,hi]
#print axioms markedExitIncrement
end models
end PA194MarkedExitIncrement
