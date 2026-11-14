import PA194Site27ThirdDispatch
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27RootTo1
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site27ThirdDispatch PA194UnaryRuns PA194OnesCommute PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem rootTo1 (k out : M) :
    let q := out+out+1
    let w := F ones ![k+1,q]
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let z := (1 : M)+w3+w3
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let a6 := a5+a5
    F PA194Stepper.stepper ![modelNumeral M 13,F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),z4+1]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(a6+a6)+(a6+a6),F ones ![k,q]]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let q := out+out+1
  let r := F ones ![k,q]
  let w := F ones ![k+1,q]
  let w1 := w+w
  let w2 := w1+w1
  let w3 := w2+w2
  let z := (1 : M)+w3+w3
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let u0 := w+w
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
  let a5 := a4+a4
  let a6 := a5+a5
  have hw : w=r+r+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],q] = _
    rw [modelAddOne,modelOnesSucc]
  have heq : z=u3 := by
    dsimp only [z,u3,u2,u1,u0,w3,w2,w1]
    simp only [add_assoc,add_comm,add_left_comm]
  have htarget : z4+1=u6+u6+1 := by
    dsimp only [z4,z3,z2,z1,u6,u5,u4]
    rw [heq]
  change F PA194Stepper.stepper ![modelNumeral M 13,F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),z4+1]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(a6+a6)+(a6+a6),r]]
  rw [htarget]
  dsimp only [u6,u5,u4,u3,u2,u1,u0]
  rw [hw]
  exact thirteenTo1 (1 : M) r
#print axioms rootTo1
end models
end PA194Site27RootTo1
