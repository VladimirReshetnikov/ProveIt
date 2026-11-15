import PA194Site28HeaderDispatch
import PA194EightyFourTo17
import PA194RegisterPermutation
import PA194HeaderController
import PA194Site28HeaderTo17
import PA194Site28HeaderReturn
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28HeaderPass
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28HeaderDispatch PA194EightyFourTo17 PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194HeaderController BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem site28HeaderPass (k : M) (e : Fin 11 → M) :
    let v := physicalArgs e
    let f := F sourceFileCode e
    let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let r := F zeros ![k,f+f+1]
    let s := r+r
    let t0 := s+s
    let u0 := t0+t0
    let u1 := u0+u0+1
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let w := F ones ![k+1,t]
    let w1 := w+w
    let x := (w1+w1)+1
    let x1 := x+x
    let y := (x1+x1)+1
    let y1 := y+y
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let clock := (modelNumeral M 16+(((((k+1)+1)+1)+1)+((k+1)+1)))+((modelNumeral M 4+modelNumeral M 2)+rc)
    F PA194Stepper.stepper ![clock,F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),u6+u6+1]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),y4+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
  let w := F ones ![k+1,t]
  let c := modelNumeral M 16+(((((k+1)+1)+1)+1)+((k+1)+1))
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h17 := PA194Site28HeaderTo17.site28HeaderTo17 (1 : M) k e
  dsimp only at h17
  have hr := PA194Site28HeaderReturn.returnTo24 w
  dsimp only at hr
  change F PA194Stepper.stepper ![F addCode ![c,(modelNumeral M 4+modelNumeral M 2)+rc],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h17,hr]
#print axioms site28HeaderPass
end models
end PA194Site28HeaderPass
