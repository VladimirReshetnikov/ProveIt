import BusyBeaver.ZFC.ArithmeticProofWord254
import BusyBeaver.ZFC.ArithmeticCommandRun254

/-!
The exact arithmetic induction interface for proof-word correctness.

The evaluator is already total Delta1. Consequently its universal top/stack
contract is Pi1, not Pi2; IΣ1 supplies induction at that orientation. The
successor theorem below is conditional on the remaining exact twelve-case
numeric row proof. No compiled-proof execution or consistency endpoint is
asserted until that step is separately discharged.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticProofWordContract254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandRun254
open ArithmeticProofWord254
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance value_delta : 𝚫₁-Function₁[V] ArithmeticHistory254.value :=
  ArithmeticHistory254.value_defined_delta.to_definable
private instance rawWord_delta : 𝚫₁-Function₁[V] rawWord :=
  rawWord_defined_delta.to_definable
private instance state_delta : 𝚫₁-Function₄[V] stateValue :=
  state_defined.graph_delta.to_definable
private instance someState_delta : 𝚫₁-Function₄[V] someState :=
  someState_defined.graph_delta.to_definable
private instance eval_delta : 𝚫₁-Function₂[V] evalValue :=
  eval_defined_delta.to_definable

/-- Exactly the old halt-or-success contract, with coded all-internal inputs. -/
def Contract (word target : V) : Prop :=
  ∀ top stack, evalValue word (stateValue top stack 0 0) = 0 ∨
    evalValue word (stateValue top stack 0 0) = someState target stack 0 0

/-- Invalid nodes are vacuous. Accepted nodes retain the validator's exact
conclusion minus its validity marker, and every arbitrary saved stack. -/
def Good (code : V) : Prop :=
  ArithmeticHistory254.value code = 0 ∨
    Contract (rawWord code) (ArithmeticHistory254.value code - 1)

def PrefixGood (code : V) : Prop := ∀ i ≤ code, Good i

instance good_definable : 𝚷₁-Predicate (Good (V := V)) := by
  unfold Good Contract
  definability

instance prefixGood_definable : 𝚷₁-Predicate (PrefixGood (V := V)) := by
  unfold PrefixGood Good Contract
  definability

lemma good_zero : Good (0 : V) := Or.inl (by simp)

/-- Extract the complete all-input contract, not just its zero-stack case. -/
lemma contract_of_good {code : V} (hc : Good code)
    (hv : ArithmeticHistory254.value code ≠ 0) :
    Contract (rawWord code) (ArithmeticHistory254.value code - 1) :=
  hc.resolve_left hv

/-- The MP major may start with a different saved stack. Universal stack
quantification remains inside the Pi1 induction hypothesis and permits it. -/
lemma major_input_of_prefix {bound child : V} (hp : PrefixGood bound)
    (hi : child ≤ bound) (hv : ArithmeticHistory254.value child ≠ 0)
    (minorTarget stack : V) :
    evalValue (rawWord child) (stateValue 0 (cantor minorTarget stack) 0 0) = 0 ∨
      evalValue (rawWord child) (stateValue 0 (cantor minorTarget stack) 0 0) =
        someState (ArithmeticHistory254.value child - 1) (cantor minorTarget stack) 0 0 :=
  contract_of_good (hp child hi) hv 0 (cantor minorTarget stack)

/-- The only remaining premise is the literal twelve-case row step. This is
an induction reduction, not an assertion that the premise already holds. -/
theorem good_of_step
    (step : ∀ raw : V, PrefixGood raw → Good (raw + 1)) :
    ∀ code : V, Good code := by
  have hp : ∀ code : V, PrefixGood code := by
    intro code
    induction code using ISigma1.pi1_succ_induction
    · exact prefixGood_definable
    case zero =>
      intro i hi
      have hz : i = 0 := le_antisymm hi (by simp)
      subst i
      exact good_zero
    case succ raw ih =>
      intro i hi
      by_cases he : i = raw + 1
      · subst i
        exact step raw ih
      · have hil : i < raw + 1 := lt_of_le_of_ne hi he
        exact ih i (lt_succ_iff_le.mp hil)
  intro code
  exact hp code code le_rfl

end SetTheory.BusyBeaver.ZFC.ArithmeticProofWordContract254
