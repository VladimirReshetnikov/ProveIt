import DiophantineConsistency.NativeCyclicCarry
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Explicit bounded iteration for finite carry systems

The quotient update starts at the zero vector. Its sum potential grows by at
least one at every nonstationary step and is bounded by `card ι * D`. Thus the
vector after exactly that many updates is stationary. No complete-lattice
fixed-point theorem or unbounded search constructs the chosen carries.

This is an arithmetic algorithm with a proved bound, not an internal HA
derivation. The predecessor map is arbitrary, including cyclic wraparound.
-/
namespace DiophantineConsistency.NativeFiniteCarry

open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {ι : Type*} [Fintype ι]

/-- Primitive recursion from the all-zero vector in a finite natural box. -/
def iterate {D : ℕ} (step : (ι → Fin (D+1)) →o (ι → Fin (D+1))) :
    ℕ → (ι → Fin (D+1))
  | 0 => fun _ => 0
  | n+1 => step (iterate step n)

def potential {D : ℕ} (k : ι → Fin (D+1)) : ℕ := ∑ i, (k i).val

theorem potential_le {D : ℕ} (k : ι → Fin (D+1)) :
    potential k ≤ Fintype.card ι * D := by
  calc
    _ ≤ ∑ _ : ι, D :=
      Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (k i).isLt)
    _ = _ := by simp

theorem eq_of_potential_eq {D : ℕ} {k l : ι → Fin (D+1)}
    (hle : k ≤ l) (heq : potential k = potential l) : k = l := by
  funext i
  apply Fin.ext
  exact (Finset.sum_eq_sum_iff_of_le
    (fun j _ => show (k j).val ≤ (l j).val from hle j)).mp heq i (Finset.mem_univ i)

omit [Fintype ι] in
theorem iterate_le_succ {D : ℕ}
    (step : (ι → Fin (D+1)) →o (ι → Fin (D+1))) (n : ℕ) :
    iterate step n ≤ iterate step (n+1) := by
  induction n with
  | zero => intro i; exact Fin.zero_le _
  | succ n ih => exact step.monotone ih

omit [Fintype ι] in
theorem iterate_monotone {D : ℕ}
    (step : (ι → Fin (D+1)) →o (ι → Fin (D+1))) : Monotone (iterate step) :=
  monotone_nat_of_le_succ (iterate_le_succ step)

/-- Every nonstationary update consumes at least one unit of finite potential. -/
theorem potential_strict {D : ℕ}
    (step : (ι → Fin (D+1)) →o (ι → Fin (D+1))) (n : ℕ)
    (hne : iterate step (n+1) ≠ iterate step n) :
    potential (iterate step n) < potential (iterate step (n+1)) := by
  have hle := iterate_le_succ step n
  have hs : potential (iterate step n) ≤ potential (iterate step (n+1)) :=
    Finset.sum_le_sum (fun i _ => hle i)
  have hn : potential (iterate step n) ≠ potential (iterate step (n+1)) :=
    fun h => hne (eq_of_potential_eq hle h).symm
  omega

theorem growth_or_fixed {D : ℕ}
    (step : (ι → Fin (D+1)) →o (ι → Fin (D+1))) (n : ℕ) :
    n ≤ potential (iterate step n) ∨ iterate step (n+1) = iterate step n := by
  induction n with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ n ih =>
      rcases ih with hg | hf
      · by_cases hf : iterate step (n+1) = iterate step n
        · exact Or.inr (congrArg step hf)
        · exact Or.inl (Nat.succ_le_of_lt (lt_of_le_of_lt hg (potential_strict step n hf)))
      · exact Or.inr (congrArg step hf)

/-- Stabilization occurs at this explicit index, including empty boxes and D=0. -/
theorem iterate_stabilizes {D : ℕ}
    (step : (ι → Fin (D+1)) →o (ι → Fin (D+1))) :
    iterate step (Fintype.card ι * D + 1) = iterate step (Fintype.card ι * D) := by
  rcases growth_or_fixed step (Fintype.card ι * D) with hg | hf
  · by_cases hf : iterate step (Fintype.card ι * D + 1) =
        iterate step (Fintype.card ι * D)
    · exact hf
    · have hs := potential_strict step (Fintype.card ι * D) hf
      have hb := potential_le (iterate step (Fintype.card ι * D + 1))
      omega
  · exact hf

omit [Fintype ι] in
theorem iterate_add_of_fixed {D : ℕ}
    (step : (ι → Fin (D+1)) →o (ι → Fin (D+1))) {n : ℕ}
    (h : iterate step (n+1) = iterate step n) (r : ℕ) :
    iterate step (n+r) = iterate step n := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change step (iterate step (n+r)) = iterate step n
      rw [ih]
      exact h

theorem iterate_stable_after {D : ℕ}
    (step : (ι → Fin (D+1)) →o (ι → Fin (D+1))) (r : ℕ) :
    iterate step (Fintype.card ι * D + r) = iterate step (Fintype.card ι * D) :=
  iterate_add_of_fixed step (iterate_stabilizes step) r

omit [Fintype ι] in
/-- The explicit iteration remains below every prefixed bounded vector. -/
theorem iterate_le_prefixed {D : ℕ}
    (step : (ι → Fin (D+1)) →o (ι → Fin (D+1)))
    (k : ι → Fin (D+1)) (hk : step k ≤ k) (n : ℕ) : iterate step n ≤ k := by
  induction n with
  | zero => intro i; exact Fin.zero_le _
  | succ n ih => exact (step.monotone ih).trans hk

/-- Chosen carries are a fixed finite number of actual quotient updates. -/
def carries (ρ D : ℕ) (hρ : 0 < ρ) (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D+1)*ρ) : ι → ℕ :=
  fun i => (iterate (NativeCyclicCarry.carryStep ρ D hρ raw prev budget)
    (Fintype.card ι * D) i).val

theorem carries_bound (ρ D : ℕ) (hρ : 0 < ρ) (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D+1)*ρ) (i : ι) :
    carries ρ D hρ raw prev budget i ≤ D :=
  Nat.le_of_lt_succ (iterate (NativeCyclicCarry.carryStep ρ D hρ raw prev budget)
    (Fintype.card ι * D) i).isLt

theorem carries_recurrence (ρ D : ℕ) (hρ : 0 < ρ) (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D+1)*ρ) (i : ι) :
    carries ρ D hρ raw prev budget i =
      (raw i + carries ρ D hρ raw prev budget (prev i))/ρ := by
  exact (congrArg (fun k : ι → Fin (D+1) => (k i).val)
    (iterate_stabilizes (NativeCyclicCarry.carryStep ρ D hρ raw prev budget))).symm

def digits (ρ D : ℕ) (hρ : 0 < ρ) (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D+1)*ρ) : ι → ℕ :=
  NativeCyclicCarry.digit ρ raw prev (carries ρ D hρ raw prev budget)

theorem normalization (ρ D : ℕ) (hρ : 0 < ρ) (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D+1)*ρ) :
    (∀ i, carries ρ D hρ raw prev budget i ≤ D) ∧
    (∀ i, digits ρ D hρ raw prev budget i < ρ) ∧
    (∀ i, carries ρ D hρ raw prev budget i =
      (raw i + carries ρ D hρ raw prev budget (prev i))/ρ) ∧
    ∀ i, raw i + carries ρ D hρ raw prev budget (prev i) =
      digits ρ D hρ raw prev budget i + ρ*carries ρ D hρ raw prev budget i :=
  ⟨carries_bound ρ D hρ raw prev budget,
    NativeCyclicCarry.digit_lt hρ raw prev _, carries_recurrence ρ D hρ raw prev budget,
    NativeCyclicCarry.carry_decomposition ρ raw prev _
      (carries_recurrence ρ D hρ raw prev budget)⟩

theorem reset (ρ D : ℕ) (hρ : 0 < ρ) (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D+1)*ρ) (i : ι) (hr : raw i + D < ρ) :
    carries ρ D hρ raw prev budget i = 0 ∧
    digits ρ D hρ raw prev budget i = raw i + carries ρ D hρ raw prev budget (prev i) :=
  NativeCyclicCarry.reset_of_bound raw prev _ (carries_bound ρ D hρ raw prev budget)
    (carries_recurrence ρ D hρ raw prev budget) i hr

theorem predecessor_reset (ρ D : ℕ) (hρ : 0 < ρ) (raw : ι → ℕ) (prev : ι → ι)
    (budget : ∀ i, raw i + D < (D+1)*ρ) (i : ι) (hr : raw (prev i) + D < ρ) :
    digits ρ D hρ raw prev budget i = raw i % ρ :=
  NativeCyclicCarry.digit_eq_mod_of_predecessor_reset raw prev _
    (carries_bound ρ D hρ raw prev budget) (carries_recurrence ρ D hρ raw prev budget) i hr

omit [Fintype ι] in
/-- The original current envelope discharges the finite carry-box budget. -/
theorem budget47 (raw : ι → ℕ)
    (hraw : ∀ i, raw i ≤ 56*2^47 + 2^46 + 1930942) :
    ∀ i, raw i + 57 < (57+1)*2^47 := by
  intro i
  exact lt_of_le_of_lt (Nat.add_le_add_right (hraw i) 57) (by decide)

def carries47 (raw : ι → ℕ) (prev : ι → ι)
    (hraw : ∀ i, raw i ≤ 56*2^47 + 2^46 + 1930942) : ι → ℕ :=
  carries (2^47) 57 (by decide) raw prev (budget47 raw hraw)

/-- Current radix47 carries stabilize after at most 57 times the field count. -/
theorem radix47_stabilizes (raw : ι → ℕ) (prev : ι → ι)
    (hraw : ∀ i, raw i ≤ 56*2^47 + 2^46 + 1930942) :
    iterate (NativeCyclicCarry.carryStep (2^47) 57 (by decide) raw prev (budget47 raw hraw))
      (Fintype.card ι * 57 + 1) =
    iterate (NativeCyclicCarry.carryStep (2^47) 57 (by decide) raw prev (budget47 raw hraw))
      (Fintype.card ι * 57) := iterate_stabilizes _

theorem radix47_normalization (raw : ι → ℕ) (prev : ι → ι)
    (hraw : ∀ i, raw i ≤ 56*2^47 + 2^46 + 1930942) :
    (∀ i, carries47 raw prev hraw i ≤ 57) ∧
    (∀ i, NativeCyclicCarry.digit (2^47) raw prev (carries47 raw prev hraw) i < 2^47) ∧
    (∀ i, carries47 raw prev hraw i = (raw i + carries47 raw prev hraw (prev i))/2^47) ∧
    ∀ i, raw i + carries47 raw prev hraw (prev i) =
      NativeCyclicCarry.digit (2^47) raw prev (carries47 raw prev hraw) i +
        2^47*carries47 raw prev hraw i :=
  normalization (2^47) 57 (by decide) raw prev (budget47 raw hraw)

theorem radix47_reset (raw : ι → ℕ) (prev : ι → ι)
    (hraw : ∀ i, raw i ≤ 56*2^47 + 2^46 + 1930942)
    (i : ι) (hr : raw i + 57 < 2^47) :
    carries47 raw prev hraw i = 0 ∧
    NativeCyclicCarry.digit (2^47) raw prev (carries47 raw prev hraw) i =
      raw i + carries47 raw prev hraw (prev i) :=
  reset (2^47) 57 (by decide) raw prev (budget47 raw hraw) i hr

end DiophantineConsistency.NativeFiniteCarry
