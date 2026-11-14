import PA194FirstMarkIncrement
import PA194IncrementSource
/-! A conditional physical path ending in a source-register increment.
The embedded increment file is already marked at the start; no theorem here
identifies that mark with the earlier q113 marker action. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstMarkIncrementSource
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194RightRows
open PA194IncrementDispatch PA194FirstMarkIncrement PA194IncrementSource PA194RegisterFile PA194MarkedFile
open PA194CarryFile PA194ReturnFile PA194RegisterPermutation PA194RegisterUpdate PA194RegisterSplit PA194DecrementSource
open PA194ControllerReturn PA194MarkerReturnCell PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- From dense 113, this specific tape layout reaches the increment entry and
updates its already-marked source-register file. The input assumes that mark;
the theorem does not identify it with the earlier q113 marking action. -/
theorem firstMarkSourceIncrement (reg : Fin 9) (e : Fin 11 → M) (u : M) :
    let p := slot reg
    let a := physicalArgs e
    let inp := inputArgs p a
    let ep := frontArgs p a (F (markedFile (8-p.val)) inp)
    let src := F (fileCode p.val) ep
    let prefixCost := F (costCode p.val) ep
    let front := (((1 : M)+1)+inp 0)+F (costCode (8-p.val)) (fun j => inp j.succ)
    let incrementCost := ((front+modelNumeral M 6)+F (costCode (8-p.val)) (fun j => inp j.succ))+((inp 0+1)+1+1)
    let boxClock := (prefixCost+incrementCost)+prefixCost
    let changed := Function.update (Function.update (Function.update e (logicalIndex reg) (inp 0+1)) 9 1) 10 0
    let out := F sourceFileCode changed
    let t0 := src+src+1
    let t1 := t0+t0
    let t2 := t1+t1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let t5 := t4+t4+1
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l := z4+z4
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let a0 := h+h+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2+1
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5
    let a7 := a6+a6
    let a8 := a7+a7
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let dispatchClock := modelNumeral M 3+(headerClock+modelNumeral M 9)
    F PA194Stepper.stepper ![dispatchClock+boxClock,
      F pairCode ![modelNumeral M 113,F pairCode ![((((l+l)+(l+l))+((l+l)+(l+l))+1)+(((l+l)+(l+l))+((l+l)+(l+l))+1)+1),(t5+t5+1)+(t5+t5+1)]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => a8),F parityCode (fun _ => a8)+(out+out)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let p := slot reg
  let a := physicalArgs e
  let inp := inputArgs p a
  let ep := frontArgs p a (F (markedFile (8-p.val)) inp)
  let src := F (fileCode p.val) ep
  let prefixCost := F (costCode p.val) ep
  let front := (((1 : M)+1)+inp 0)+F (costCode (8-p.val)) (fun j => inp j.succ)
  let incrementCost := ((front+modelNumeral M 6)+F (costCode (8-p.val)) (fun j => inp j.succ))+((inp 0+1)+1+1)
  let boxClock := (prefixCost+incrementCost)+prefixCost
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  let a0 := h+h+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2+1
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5
  let a7 := a6+a6
  let a8 := a7+a7
  let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let dispatchClock := modelNumeral M 3+(headerClock+modelNumeral M 9)
  have hd := firstMarkToIncrement u src
  dsimp only at hd
  have hb := modelSourceIncrement reg e a8
  dsimp only at hb
  change F PA194Stepper.stepper ![F addCode ![dispatchClock,boxClock],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hd]
  exact hb
#print axioms firstMarkSourceIncrement
end models
end PA194FirstMarkIncrementSource
