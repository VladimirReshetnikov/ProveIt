import PA194MarkedExitHeader
import PA194HeaderTo61
import PA194State61To2
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194MarkedExitTo2
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194MarkedExitHeader PA194HeaderTo61 PA194State61To2
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
/-- The exact marked-exit layout reaches the increment-entry control, with
its first regular block partly scanned. -/
theorem markedTo2 (u k f : M) :
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
    let left := (a3+a3)+(a3+a3)
    F PA194Stepper.stepper ![((c1+(((c2+modelNumeral M 3)+modelNumeral M 4)+1))+modelNumeral M 10),
      F pairCode ![modelNumeral M 17,F pairCode ![l+l+1,(1 : M)+f+f]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![left+left,F ones ![k,(1 : M)+f+f]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h0 := g+g+1
  let xx := h0+h0+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a := F ones ![k+1,(1 : M)+f+f]
  let q := F ones ![k,(1 : M)+f+f]
  let z := a+a
  let c1 := ((((k+1)+1)+1)+1)+1+((modelNumeral M 3+1)+1)
  let c2 := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have ha : a = q+q+1 := by
    dsimp only [a,q]
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h := markedToHeader u k f
  dsimp only at h
  have h4 (x : M) : F ones ![modelNumeral M 3+1,x] =
      F ones ![modelNumeral M 3,x]+F ones ![modelNumeral M 3,x]+1 := by
    change F ones ![F addCode ![modelNumeral M 3,F oneCode Fin.elim0],x] = _
    rw [modelAddOne,modelOnesSucc]
  rw [h4] at h
  have hc (x : M) : (1 : M)+(x+x)+(x+x) = (x+x)+(x+x)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hc] at h
  have h61 := nextHeaderTo61 u z
  dsimp only at h61
  have h2 := state61To2 a2 q
  dsimp only at h2
  change F PA194Stepper.stepper ![F addCode ![c1+(((c2+modelNumeral M 3)+modelNumeral M 4)+1),modelNumeral M 10],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 10,F PA194Stepper.stepper ![F addCode ![c1,((c2+modelNumeral M 3)+modelNumeral M 4)+1],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h,h61]
  change F PA194Stepper.stepper ![modelNumeral M 10,F pairCode ![modelNumeral M 61,
    F pairCode ![(a2+a2+1)+(a2+a2+1),z]]] = _
  have hz : z = (q+q+1)+(q+q+1) := by dsimp only [z]; rw [ha]
  rw [hz]
  exact h2
#print axioms markedTo2
end models
end PA194MarkedExitTo2
