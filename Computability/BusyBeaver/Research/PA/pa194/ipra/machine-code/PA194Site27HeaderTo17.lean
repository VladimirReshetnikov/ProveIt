import PA194Site27HeaderDispatch
import PA194EightyFourTo17
import PA194RegisterPermutation
import PA194HeaderController
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27HeaderTo17
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

theorem site27HeaderTo17 (l k : M) (e : Fin 11 → M) :
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
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let w := F ones ![k+1,t]
    let clock := modelNumeral M 13+(((((k+1)+1)+1)+1)+((k+1)+1))
    F PA194Stepper.stepper ![clock,F pairCode ![modelNumeral M 24,F pairCode ![l,u6+u6+1]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![a4,(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs e
  let f := F sourceFileCode e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let r := F zeros ![k,f+f+1]
  let a0 := l+l+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let c := (((((k+1)+1)+1)+1)+((k+1)+1))
  have hf : f=p+p := by rw [show f = F (fileCode 10) v from modelSourceFile e,modelFileSucc,modelBlock]
  have ht : f+f+1 = (1 : M)+(p+p)+(p+p) := by rw [hf]; simp only [add_comm,add_left_comm]
  have h84 := thirteenSteps l r
  dsimp only at h84
  have h17 := returnedFileTo17 k a5 p
  dsimp only at h17
  rw [←ht,zerosTwo,(modelDouble a4).1,(modelDouble a4).2,zero_add] at h17
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 13,c],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h84,h17]
#print axioms site27HeaderTo17
end models
end PA194Site27HeaderTo17
