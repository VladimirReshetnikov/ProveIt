import PA194Site27HeaderDispatch
import PA194EightyFourTo17
import PA194RegisterPermutation
import PA194HeaderController
import PA194Site27HeaderTo17
import PA194Site27HeaderReturn
import PA194Site27HeaderPass
import PA194Site27SecondDispatch
import PA194Site27To106
import PA194Site27Scan106
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27To71
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site27HeaderDispatch PA194EightyFourTo17 PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194HeaderController BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem site27To71 (k : M) (e : Fin 11 → M) :
    let v := physicalArgs e
    let f := F sourceFileCode e
    let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let r := F zeros ![k,f+f+1]
    let s := r+r
    let u0 := s+s
    let u1 := u0+u0
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let w := F ones ![k+1,t]
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let x := w3+1
    let x1 := x+x
    let x2 := x1+x1
    let x3 := x2+x2
    let x4 := x3+x3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let rhalf := F ones ![k,t]
    let aa0 := (1 : M)+(1 : M)+1
    let aa1 := aa0+aa0
    let aa2 := aa1+aa1
    let aa3 := aa2+aa2
    let aa4 := aa3+aa3+1
    let aa5 := aa4+aa4
    let aa6 := aa5+aa5
    let n := (k+1)+1
    let a := F ones ![n,aa6+aa6]
    let clock := (((modelNumeral M 13+(((((k+1)+1)+1)+1)+((k+1)+1)))+(modelNumeral M 5+rc))+modelNumeral M 8)+(n+1)
    F PA194Stepper.stepper ![clock,F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),u6+u6+1]]] =
    F pairCode ![modelNumeral M 71,F pairCode ![a+a,p]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
  let w := F ones ![k+1,t]
  let c := modelNumeral M 13+(((((k+1)+1)+1)+1)+((k+1)+1))
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let rhalf := F ones ![k,t]
  let aa0 := (1 : M)+(1 : M)+1
  let aa1 := aa0+aa0
  let aa2 := aa1+aa1
  let aa3 := aa2+aa2
  let aa4 := aa3+aa3+1
  let aa5 := aa4+aa4
  let aa6 := aa5+aa5
  let n := (k+1)+1
  have h := PA194Site27To106.site27To106 k e
  dsimp only at h
  have h71 := PA194Site27Scan106.scan106To71 k (aa6+aa6) p
  dsimp only at h71
  change F PA194Stepper.stepper ![F addCode ![(c+(modelNumeral M 5+rc))+modelNumeral M 8,n+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h,h71]
#print axioms site27To71
end models
end PA194Site27To71
