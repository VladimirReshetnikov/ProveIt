import Mathlib.Data.Fintype.Order
import Mathlib.Order.FixedPoints

/-!
# Bounded cyclic carries before native interpretation

A local raw digit may exceed the radix. A bound on the *next carry*,
rather than a global no-carry assumption, supplies a simultaneous carry
assignment. The predecessor map may be cyclic; no starting carry is fixed
to zero. The theorem works for any predecessor map, which also covers
every finite cyclic word and its last-to-first carry.

Only a numeric carry budget is assumed. No tile decoding, temporal
alignment, native-equation correctness or consistency premise occurs.
The fixed-point construction does not assert uniqueness: the zero and
all-maximum-digit representatives can require a later strict-word bound.
-/

namespace DiophantineConsistency.NativeCyclicCarry

variable {ι : Type*}

/-- The quotient update on the entire bounded carry box. -/
def carryStep (ρ D : ℕ) (hρ : 0 < ρ) (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D + 1) * ρ) :
    (ι → Fin (D + 1)) →o (ι → Fin (D + 1)) where
  toFun k i := ⟨(raw i + (k (prev i)).val) / ρ, by
    apply (Nat.div_lt_iff_lt_mul hρ).mpr
    exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_of_lt_succ (k (prev i)).isLt) _)
      (budget i)⟩
  monotone' := by
    intro k l h i
    exact Nat.div_le_div_right (Nat.add_le_add_left (h (prev i)) _)

/-- Simultaneous bounded carries exist even when the predecessor relation
wraps around. The equality is the actual quotient recurrence. -/
theorem exists_bounded_carries (ρ D : ℕ) (hρ : 0 < ρ)
    (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D + 1) * ρ) :
    ∃ k : ι → ℕ, (∀ i, k i ≤ D) ∧
      ∀ i, k i = (raw i + k (prev i)) / ρ := by
  let step := carryStep ρ D hρ raw prev budget
  let k := step.lfp
  refine ⟨fun i => (k i).val, fun i => Nat.le_of_lt_succ (k i).isLt, ?_⟩
  intro i
  have h := congrArg (fun x : ι → Fin (D + 1) => (x i).val) step.map_lfp
  exact h.symm

/-- The digit belonging to an actual carry assignment. -/
def digit (ρ : ℕ) (raw : ι → ℕ) (prev : ι → ι) (k : ι → ℕ) (i : ι) : ℕ :=
  (raw i + k (prev i)) % ρ

theorem digit_lt {ρ : ℕ} (hρ : 0 < ρ) (raw : ι → ℕ)
    (prev : ι → ι) (k : ι → ℕ) (i : ι) : digit ρ raw prev k i < ρ :=
  Nat.mod_lt _ hρ

/-- Exact digit/carry decomposition, not just a modular assertion. -/
theorem carry_decomposition (ρ : ℕ) (raw : ι → ℕ) (prev : ι → ι)
    (k : ι → ℕ) (hk : ∀ i, k i = (raw i + k (prev i)) / ρ) (i : ι) :
    raw i + k (prev i) = digit ρ raw prev k i + ρ * k i := by
  rw [hk i]
  exact (Nat.mod_add_div _ _).symm

/-- The full bounded normalization interface, before any native semantics. -/
theorem exists_bounded_digits (ρ D : ℕ) (hρ : 0 < ρ)
    (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D + 1) * ρ) :
    ∃ k digits : ι → ℕ, (∀ i, k i ≤ D) ∧ (∀ i, digits i < ρ) ∧
      (∀ i, k i = (raw i + k (prev i)) / ρ) ∧
      ∀ i, raw i + k (prev i) = digits i + ρ * k i := by
  obtain ⟨k, hbound, hk⟩ := exists_bounded_carries ρ D hρ raw prev budget
  exact ⟨k, digit ρ raw prev k, hbound, digit_lt hρ raw prev k,
    hk, carry_decomposition ρ raw prev k hk⟩

/-- The exact raw envelope used in the current radix47 ordinary proof
fits the carry box0..57, without a no-carry assumption. The envelope
itself remains an explicit premise to be proved from the native kernel. -/
theorem radix47_carry57 (raw : ι → ℕ) (prev : ι → ι)
    (hraw : ∀ i, raw i ≤ 56 * 2^47 + 2^46 + 1930942) :
    ∃ k digits : ι → ℕ, (∀ i, k i ≤ 57) ∧ (∀ i, digits i < 2^47) ∧
      (∀ i, k i = (raw i + k (prev i)) / 2^47) ∧
      ∀ i, raw i + k (prev i) = digits i + 2^47 * k i := by
  apply exists_bounded_digits (2^47) 57 (by decide) raw prev
  intro i
  exact lt_of_le_of_lt (Nat.add_le_add_right (hraw i) 57) (by decide)

/-- A local budget below one radix resets its outgoing carry. This applies
to every bounded solution of the recurrence, not only the chosen fixed point. -/
theorem reset_of_bound {ρ D : ℕ} (raw : ι → ℕ) (prev : ι → ι)
    (k : ι → ℕ) (hbound : ∀ i, k i ≤ D)
    (hk : ∀ i, k i = (raw i + k (prev i)) / ρ)
    (i : ι) (hreset : raw i + D < ρ) :
    k i = 0 ∧ digit ρ raw prev k i = raw i + k (prev i) := by
  have hsmall : raw i + k (prev i) < ρ :=
    lt_of_le_of_lt (Nat.add_le_add_left (hbound (prev i)) _) hreset
  exact ⟨(hk i).trans (Nat.div_eq_of_lt hsmall), Nat.mod_eq_of_lt hsmall⟩

/-- After a predecessor reset, the next tested digit has no incoming carry,
even if that next field itself produces an outgoing carry. -/
theorem digit_eq_mod_of_predecessor_reset {ρ D : ℕ}
    (raw : ι → ℕ) (prev : ι → ι) (k : ι → ℕ)
    (hbound : ∀ i, k i ≤ D)
    (hk : ∀ i, k i = (raw i + k (prev i)) / ρ)
    (i : ι) (hreset : raw (prev i) + D < ρ) :
    digit ρ raw prev k i = raw i % ρ := by
  have hzero := (reset_of_bound raw prev k hbound hk (prev i) hreset).1
  simp only [digit, hzero, Nat.add_zero]

end DiophantineConsistency.NativeCyclicCarry
