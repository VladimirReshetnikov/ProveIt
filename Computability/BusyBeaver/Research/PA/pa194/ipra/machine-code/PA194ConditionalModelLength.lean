import PA194StepperCompose
import Foundation.FirstOrder.Arithmetic.Induction
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ConditionalModelLength
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194Stepper PA194StepperCompose
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Conditional model-length lockstep with a possibly state-dependent finite
literal clock. The Σ₁ condition is an explicit hypothesis, to be discharged
using primitive-recursive graphs and the concrete store invariant. -/
theorem simulateModelLength
    (state next frame elapsed cost : M → M) (good : M → Prop) (start : M)
    (hdef : 𝚺₁-Predicate (fun n : M => good (state n) ∧
      F stepper ![elapsed n,start] = frame (state n)))
    (hbase : good (state 0) ∧ F stepper ![elapsed 0,start] = frame (state 0))
    (hnext : ∀ n, state (n+1) = next (state n))
    (hclock : ∀ n, elapsed (n+1) = F addCode ![elapsed n,cost (state n)])
    (hpres : ∀ s, good s → good (next s))
    (hsegment : ∀ s, good s → F stepper ![cost s,frame s] = frame (next s)) :
    ∀ n, good (state n) ∧ F stepper ![elapsed n,start] = frame (state n) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero => exact hbase
  | succ n ih =>
    constructor
    · rw [hnext]
      exact hpres (state n) ih.1
    · rw [hnext,hclock,modelStepperCompose,ih.2,hsegment (state n) ih.1]
#print axioms simulateModelLength
end models
end PA194ConditionalModelLength
