import PA194ZeroReturnTo16
import PA194Site27PositiveReturnFrom16
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27PositiveReturnTo24
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194ZeroReturnTo16 PA194Site27PositiveReturnFrom16 PA194ZeroRuns PA194BinaryDouble BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem returnTo24 (k p : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let l := a5+a5+1
    let lzero := F zeros ![modelNumeral M 2,l]
    let left := F zeros ![k+1,lzero+lzero]
    let z := F zeros ![k+1,(1 : M)+(p+p)+(p+p)]
    let r := (z+z)+(z+z)
    let x := (1+1)+(r+r)+(r+r)
    let t := (1 : M)+x+x
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let c1 := ((1 : M)+(k+1))+modelNumeral M 3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![c1+(modelNumeral M 2+(modelNumeral M 3+rc)),
      F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => left),F parityCode (fun _ => left)+(p+p)+(p+p)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let z := F zeros ![k+1,(1 : M)+(p+p)+(p+p)]
  let r := (z+z)+(z+z)
  let c1 := ((1 : M)+(k+1))+modelNumeral M 3
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h16 := from14To16 k a5 p
  dsimp only at h16
  rw [(modelDouble a4).1,(modelDouble a4).2,zero_add] at h16
  have h24 := returnFrom16 r
  dsimp only at h24
  change F PA194Stepper.stepper ![F addCode ![c1,modelNumeral M 2+(modelNumeral M 3+rc)],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h16,h24]
#print axioms returnTo24
end models
end PA194Site27PositiveReturnTo24
