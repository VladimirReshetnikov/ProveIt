import OAI.Combinatorics.Progressions.Estimates.PhysicalStabilityParameters

namespace OAI

section

namespace Erdos3.PhysicalEpochStack

open scoped BigOperators

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem BudgetedAt.periods_product_le {A C : ℕ} {U : ℝ} {stack : PhysicalEpochStack base}
    (h : BudgetedAt A U C stack) : (stack.periods.prod : ℝ) ≤ Real.exp ((s : ℝ) * U) := by
  induction stack with
  | zero => simp [periods]
  | @succ t base frame tail ih =>
    obtain ⟨_, _, _, hperiod, _, _, ht⟩ := h
    change ((frame.period * tail.periods.prod : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul]
    calc
      (frame.period : ℝ) * tail.periods.prod ≤ Real.exp U * Real.exp ((t : ℝ) * U) :=
        mul_le_mul hperiod (ih ht) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (((t + 1 : ℕ) : ℝ) * U) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

theorem BudgetedAt.period_exclusions_card_le {A C : ℕ} {U : ℝ} {stack : PhysicalEpochStack base}
    (h : BudgetedAt A U C stack) {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime) :
    ((periodPrimeCoordinates prime stack.periods.prod).card : ℝ) ≤ 2 * ((s : ℝ) * U) :=
  periodPrimeCoordinates_card_le prime hprime hinj stack.periods_product_pos h.periods_product_le

theorem BudgetedAt.new_period_exclusions_card_le {A C : ℕ} {U : ℝ} {stack : PhysicalEpochStack base}
    (h : BudgetedAt A U C stack) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime) (selected : Finset ι) :
    (((periodPrimeCoordinates prime stack.periods.prod) \ selected).card : ℝ) ≤ 2 * ((s : ℝ) * U) := by
  have hcard : ((periodPrimeCoordinates prime stack.periods.prod) \ selected).card ≤
      (periodPrimeCoordinates prime stack.periods.prod).card := Finset.card_le_card Finset.sdiff_subset
  exact (Nat.cast_le.mpr hcard).trans (h.period_exclusions_card_le prime hprime hinj)

theorem pending_coprime_selected_periods (stack : PhysicalEpochStack base)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (selected pending : Finset ι)
    (hdisjoint : Disjoint pending (selected ∪ periodPrimeCoordinates prime stack.periods.prod)) :
    ((∏ i ∈ selected, prime i ^ power i) * stack.periods.prod).Coprime
      (∏ i ∈ pending, prime i ^ power i) :=
  (periodPrimeCoordinates_unfixed_coprime prime power hprime hinj stack.periods.prod selected pending hdisjoint).symm

end Erdos3.PhysicalEpochStack

end

end OAI
