import PA194Site27ZeroTo5
import PA194DecrementZeroCell
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroTo11
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open PRAModelIOpenPairing PA194BinaryDouble PA194DecrementZeroCell PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem fiveTo11 (z u : M) :
    let t := u+u+1
    F PA194Stepper.stepper ![modelNumeral M 2,
      F pairCode ![modelNumeral M 5,F pairCode ![(z+z)+(z+z)+1,t]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![z,(t+t)+(t+t)]] := by
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,packedFive]
  have hr : (u+u)+(u+u)+(1+1)+1 = (u+u+1)+(u+u+1)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hr,packedEight,(modelDouble z).1,(modelDouble z).2]
  simp only [zero_add]

theorem zeroTo11 (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    let v := physicalArgs e
    let e1 : Fin 10 → M := fun j => v j.succ
    let e2 : Fin 9 → M := fun j => e1 j.succ
    let e3 : Fin 8 → M := fun j => e2 j.succ
    let e4 : Fin 7 → M := fun j => e3 j.succ
    let e5 : Fin 6 → M := fun j => e4 j.succ
    let e6 : Fin 5 → M := fun j => e5 j.succ
    let t := F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
    ∃ clock carried : M, let z := carried+carried+1
      F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
        F pairCode ![modelNumeral M 11,F pairCode ![z,(t+t)+(t+t)]] := by
  dsimp only
  let v := physicalArgs e
  let e1 : Fin 10 → M := fun j => v j.succ
  let e2 : Fin 9 → M := fun j => e1 j.succ
  let e3 : Fin 8 → M := fun j => e2 j.succ
  let e4 : Fin 7 → M := fun j => e3 j.succ
  let e5 : Fin 6 → M := fun j => e4 j.succ
  let e6 : Fin 5 → M := fun j => e5 j.succ
  let t := F ones ![e6 1+1,F (fileCode 2) (fun i => e6 i.succ.succ)]
  let u := F ones ![e6 1,F (fileCode 2) (fun i => e6 i.succ.succ)]
  have ht : t = u+u+1 := by
    dsimp only [t,u]
    rw [show e6 1+1 = F Code.succ (fun _ => e6 1) from modelAddOne _,modelOnesSucc]
  obtain ⟨clock,carried,h5⟩ := PA194Site27ZeroTo5.zeroTo5 k e hz
  dsimp only at h5
  let z := carried+carried+1
  have h11 := fiveTo11 z u
  dsimp only at h11
  rw [←ht] at h11
  refine ⟨F addCode ![clock,modelNumeral M 2],carried,?_⟩
  rw [PA194StepperCompose.modelStepperCompose,h5]
  exact h11
#print axioms fiveTo11
#print axioms zeroTo11
end models
end PA194Site27ZeroTo11
