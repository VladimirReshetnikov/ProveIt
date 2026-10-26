import DiophantineConsistency.ObjectNaturalDiscrete
import Mathlib.Algebra.Order.SuccPred

/-!
Source-level prototype, not compiler-checked in this session.
The proposed production home for val_add_one is ObjectOmegaSemiring.Natural.
The order bridges can precede lt_iff_exists_add_one in ObjectNaturalDiscrete:
none uses that theorem or zero_or_add_one.  We import the existing completed
module here solely to make this candidate independently replayable.
-/

namespace ProofDelta.InternalSuccessor
open DiophantineConsistency
open SetTheory
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication
open ObjectMultiplicationLaws ObjectOmegaSemiring

universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

theorem val_add_one (x : N H) : (x + 1).val = vsucc H x.val := by
  change addValue H x.val (vsucc H (vempty H)) = vsucc H x.val
  rw [addValue_succ_right H x.property (vempty_in_omega H),
    addValue_zero_right H x.property]

-- Uses only the literal set-successor membership law and linear order.
-- The conversion of the equality branch is explicit, so the proof does not
-- assume that the existing <= implementation reduces to a particular Or.
theorem internal_lt_add_one_iff (a b : N H) : a < b + 1 ↔ a ≤ b := by
  change mem a.val (b + 1).val ↔ a ≤ b
  rw [val_add_one H b, vsucc_spec H b.val a.val]
  constructor
  · rintro (h | h)
    · exact le_of_lt h
    · exact le_of_eq (Subtype.ext h)
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr (congrArg Subtype.val h)

theorem internal_add_one_le_iff (a b : N H) : a + 1 ≤ b ↔ a < b := by
  rw [← not_lt, internal_lt_add_one_iff H b a, not_le]

-- These definitions are local instances in the prototype to avoid silently
-- changing a client's instance environment. A maintained successor module
-- could expose one coherent instance of each after integration checks.
noncomputable def naturalSuccAddOrder : SuccAddOrder (N H) where
  toSuccOrder := SuccOrder.ofSuccLeIff (fun x => x + 1)
    (fun {a b} => internal_add_one_le_iff H a b)
  succ_eq_add_one _ := rfl

def naturalNoMaxOrder : NoMaxOrder (N H) where
  exists_gt a := ⟨a + 1, (internal_lt_add_one_iff H a a).mpr le_rfl⟩

attribute [local instance] naturalSuccAddOrder naturalNoMaxOrder

-- Replacement for the long difference-and-predecessor argument.
theorem lt_iff_exists_add_one (x y : N H) :
    x < y ↔ ∃ s : N H, y = x + s + 1 := by
  rw [← Order.add_one_le_iff, ObjectNaturalOrder.Natural.le_iff_exists_add H]
  apply exists_congr
  intro s
  simpa only [add_right_comm x 1 s] using
    (eq_comm : (x + s + 1 = y) ↔ (y = x + s + 1))

-- Exact old add_one_le_of_lt interface used in ObjectPairingSurjective.
theorem pairing_successor_bound {a b : N H} (h : a < b) : a + 1 ≤ b :=
  Order.add_one_le_of_lt h

-- This is the succ_le callback consumed by MaxSquarePairing.pair_eq_pair_iff.
theorem pairing_injectivity_callback : ∀ a b : N H, a < b → a + 1 ≤ b :=
  fun _ _ h => Order.add_one_le_of_lt h

-- Direct replacement for the separately expanded subtype successor equality
-- inside ObjectDivision.division_exists and pair_surjective's induction step.
theorem lifted_successor (x : V) (hx : mem x (omegaV H)) :
    (⟨vsucc H x, omega_succ H x hx⟩ : N H) = (⟨x, hx⟩ : N H) + 1 :=
  Subtype.ext (val_add_one H ⟨x, hx⟩).symm

#print axioms internal_lt_add_one_iff
#print axioms lt_iff_exists_add_one
#print axioms lifted_successor

end ProofDelta.InternalSuccessor
