import Sharma2012.AsymptoticConsequences

/-!
# Conditional upper-bound consequences for Sharma's counting function

This module isolates the short analytic part of Sharma's upper-bound
argument.  The structural recurrence in Theorem 2.8 is supplied explicitly
as a hypothesis, so the dependency remains visible in every result below.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace LeanProofs.Sharma2012

/-- Sum a pointwise bound over the pairs induced by a finite equivalence.
No fixed-point-free hypothesis is needed: fixed points simply contribute
twice their own weight. -/
theorem twice_sum_le_of_equiv_pair_bound
    {α : Type*} [Fintype α] (pair : α ≃ α)
    (weight : α → Nat) (bound : Nat)
    (hpair : ∀ x, weight x + weight (pair x) ≤ bound) :
    2 * ∑ x, weight x ≤ bound * Fintype.card α := by
  have hreindex : (∑ x, weight (pair x)) = ∑ x, weight x :=
    pair.sum_comp weight
  calc
    2 * ∑ x, weight x = (∑ x, weight x) + ∑ x, weight (pair x) := by
      rw [hreindex]
      omega
    _ = ∑ x, (weight x + weight (pair x)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ _x : α, bound := Finset.sum_le_sum fun x _hx => hpair x
    _ = bound * Fintype.card α := by simp [Nat.mul_comm]

/-- The certified table gives Sharma's `2.7` upper bound on the finite
interval from `11` through `20`. -/
theorem theta_le_twenty_seven_tenths_pow_on_eleven_twenty (n : Nat)
    (hlo : 11 ≤ n) (hhi : n ≤ 20) :
    (theta n : Real) ≤ ((27 : Real) / 10) ^ n / 21 := by
  have htable := theta_values_through_twenty
  have hentry := congrArg (fun values : List Nat => values[n - 1]?) htable
  interval_cases n <;> norm_num at hentry ⊢ <;> norm_num [hentry]

/-- The proved insertion bound at `n = 20` supplies the additional base
value at `n = 21` needed by the recurrence induction. -/
theorem theta_le_twenty_seven_tenths_pow_at_twenty_one :
    (theta 21 : Real) ≤ ((27 : Real) / 10) ^ (21 : Nat) / 21 := by
  have hins :=
    LeanProofs.DavisEntringerGrahamSimmons1977.insertion_count_upper_bound_holds
      20 (by norm_num)
  have hinsTheta : theta 21 ≤ 11 * theta 20 := by
    simpa only [theta_eq_davis_count] using hins
  have htable := theta_values_through_twenty
  have hentry := congrArg (fun values : List Nat => values[19]?) htable
  norm_num at hentry
  rw [hentry] at hinsTheta
  norm_num at hinsTheta
  have hinsReal : (theta 21 : Real) ≤ 32308496 := by
    exact_mod_cast hinsTheta
  exact hinsReal.trans (by norm_num)

/-- A reusable balanced-recurrence induction.  The identity
`ceil(n / 2) + floor(n / 2) = n` recombines the two exponential estimates. -/
theorem balanced_recurrence_exponential_bound
    (a : Nat → Nat) (c : Real) (hc : 0 ≤ c)
    (hbase : ∀ n : Nat, 11 ≤ n → n < 22 →
      (a n : Real) ≤ c ^ n / 21)
    (hrec : ∀ n : Nat, 22 ≤ n →
      a n ≤ 21 * a ((n + 1) / 2) * a (n / 2)) :
    ∀ n : Nat, 11 ≤ n → (a n : Real) ≤ c ^ n / 21 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hnSmall : n < 22
      · exact hbase n hn hnSmall
      · have hnLarge : 22 ≤ n := by omega
        have hfloorLo : 11 ≤ n / 2 := by omega
        have hceilLo : 11 ≤ (n + 1) / 2 := by omega
        have hfloorLt : n / 2 < n := by omega
        have hceilLt : (n + 1) / 2 < n := by omega
        have hfloor := ih (n / 2) hfloorLt hfloorLo
        have hceil := ih ((n + 1) / 2) hceilLt hceilLo
        have hrecReal : (a n : Real) ≤
            21 * (a ((n + 1) / 2) : Real) * (a (n / 2) : Real) := by
          exact_mod_cast hrec n hnLarge
        calc
          (a n : Real) ≤
              21 * (a ((n + 1) / 2) : Real) * (a (n / 2) : Real) := hrecReal
          _ ≤ 21 * (c ^ ((n + 1) / 2) / 21) * (c ^ (n / 2) / 21) := by
            gcongr
          _ = (c ^ ((n + 1) / 2) * c ^ (n / 2)) / 21 := by ring
          _ = c ^ (((n + 1) / 2) + n / 2) / 21 := by rw [pow_add]
          _ = c ^ n / 21 := by
            have hsum : (n + 1) / 2 + n / 2 = n := by omega
            rw [hsum]

/-- **Theorem 2.9**, conditional on the structural recurrence asserted by
Theorem 2.8. -/
theorem theorem_2_9_of_theorem_2_8 (h28 : theorem_2_8) : theorem_2_9 := by
  apply balanced_recurrence_exponential_bound theta
    ((27 : Real) / 10) (by norm_num)
  · intro n hlo hhi
    by_cases hn : n = 21
    · subst n
      exact theta_le_twenty_seven_tenths_pow_at_twenty_one
    · exact theta_le_twenty_seven_tenths_pow_on_eleven_twenty n hlo (by omega)
  · intro n hn
    exact h28 n (by omega)

/-- Taking a positive integral root preserves a nonnegative upper bound by
the corresponding integral power. -/
theorem rpow_inv_natCast_le_of_le_pow
    {x c : Real} {n : Nat} (hn : n ≠ 0)
    (hx : 0 ≤ x) (hc : 0 ≤ c) (hxc : x ≤ c ^ n) :
    x ^ (n : Real)⁻¹ ≤ c := by
  calc
    x ^ (n : Real)⁻¹ ≤ (c ^ n) ^ (n : Real)⁻¹ :=
      Real.rpow_le_rpow hx hxc (by positivity)
    _ = c := Real.pow_rpow_inv_natCast hc hn

/-- Theorem 2.9 gives the eventual pointwise upper bound on Sharma's
exponential-rate sequence. -/
theorem exponentialRate_le_twenty_seven_tenths
    (h29 : theorem_2_9) {n : Nat} (hn : 11 ≤ n) :
    exponentialRate n ≤ (27 : Real) / 10 := by
  have htheta := h29 n hn
  have hpowNonneg : 0 ≤ ((27 : Real) / 10) ^ n := by positivity
  have hthetaPow : (theta n : Real) ≤ ((27 : Real) / 10) ^ n := by
    calc
      (theta n : Real) ≤ ((27 : Real) / 10) ^ n / 21 := htheta
      _ ≤ ((27 : Real) / 10) ^ n := by nlinarith
  unfold exponentialRate
  exact rpow_inv_natCast_le_of_le_pow (by omega)
    (by positivity) (by norm_num) hthetaPow

/-- **Theorem 2.10**, conditional on Theorem 2.9. -/
theorem theorem_2_10_of_theorem_2_9 (h29 : theorem_2_9) : theorem_2_10 := by
  unfold theorem_2_10
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by
      unfold exponentialRate
      exact Real.rpow_nonneg (by positivity) _)
  · filter_upwards [eventually_ge_atTop 11] with n hn
    exact exponentialRate_le_twenty_seven_tenths h29 hn

/-- **Theorem 2.10**, conditional directly on Theorem 2.8 through the
derived proof of Theorem 2.9. -/
theorem theorem_2_10_of_theorem_2_8 (h28 : theorem_2_8) : theorem_2_10 :=
  theorem_2_10_of_theorem_2_9 (theorem_2_9_of_theorem_2_8 h28)

end LeanProofs.Sharma2012
