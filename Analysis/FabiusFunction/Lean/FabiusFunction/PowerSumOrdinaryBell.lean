import FabiusFunction.NewtonPowerSumBell

/-!
# The power sums through the *ordinary* partial Bell polynomials

The source gives two forms of the power-sum identity.  `NewtonPowerSumBell` proves the first,
through the exponential partial Bell polynomials.  This module proves the second,

`p_n = (-1)^n n ∑_{k=1}^{n} (1/k) B̂_{n,k}(-e_1, -e_2, …)`   (`power_sum_eq_ord_bell`),

where `B̂` is the ordinary partial Bell polynomial, and with it closes the theorem.

Both forms come from the same series, read two ways.  `log E` has the Newton weights as its
*exponential* coefficients — that is `CumulantBellFormula` — and expanding the same logarithm
by substitution gives its coefficients as a sum over powers of `E - 1`, whose coefficients the
corpus reads off as *ordinary* partial Bell polynomials
(`coeff_subst_eq_sum_ordPartialBell`).  Equating the two readings is the whole proof; the
`(-1)^k` that turns `B̂(e)` into `B̂(-e)` is the homogeneity `ordPartialBell_mul_left`.

This is the payoff for having proved `exp(log f) = f` in general rather than working around it:
the exponential reading and the ordinary reading of `log E` are now both available, and the
identity between them costs nothing further.

## Main results

* `coeff_logOf_elemSeries`, the exponential reading.
* `coeff_logOf_elemSeries_ord`, the ordinary reading.
* `power_sum_eq_ord_bell`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section OrdBell

variable {ι : Type*} (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The elementary symmetric generating function is the exponential generating function of
the scaled elementary symmetric functions. -/
theorem elemSeries_eq_egfA_scaled (s : Finset ι) (u : ι → A) :
    elemSeries A s u = egfA A (scaledElemSym A s u) := by
  rw [elemSeries_eq_egfA_bell_complete, complete_newtonWeight]

/-- `E` has constant term `1`. -/
theorem constantCoeff_elemSeries' (s : Finset ι) (u : ι → A) :
    constantCoeff (elemSeries A s u) = 1 := constantCoeff_elemSeries A s u

/-- **The exponential reading:** `log E` has the Newton weights as exponential
coefficients. -/
theorem coeff_logOf_elemSeries (s : Finset ι) (u : ι → A) (n : ℕ) :
    coeff n (logOf (elemSeries A s u)) =
      algebraMap ℚ A (1 / n.factorial) * newtonWeight A s u n := by
  have hcum : Bell.cumulant (scaledElemSym A s u) = cumulantSum A (scaledElemSym A s u) :=
    cumulant_eq_cumulantSum A _ (scaledElemSym_zero A s u)
  have hnew : newtonWeight A s u = cumulantSum A (scaledElemSym A s u) := by
    rw [← hcum]
    exact Bell.eq_cumulant_of_complete (by rw [newtonWeight, if_pos rfl])
      (complete_newtonWeight A s u)
  rw [elemSeries_eq_egfA_scaled, coeff_logOf_egfA A _ (scaledElemSym_zero A s u), hnew]

/-- **The ordinary reading:** expanding the same logarithm by substitution. -/
theorem coeff_logOf_elemSeries_ord (s : Finset ι) (u : ι → A) (n : ℕ) :
    coeff n (logOf (elemSeries A s u)) =
      ∑ k ∈ Finset.range (n + 1), coeff k (log A) *
        ordPartialBell (fun j => ∑ t ∈ s.powersetCard j, ∏ i ∈ t, u i) n k := by
  have hE1 : constantCoeff (elemSeries A s u - 1) = 0 := by
    rw [map_sub, constantCoeff_elemSeries, map_one, sub_self]
  rw [logOf_eq, coeff_subst_eq_sum_ordPartialBell (log A) hE1 n]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine ordPartialBell_congr (fun i hi => ?_) n k
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [map_sub, coeff_elemSeries, coeff_one, if_neg (Nat.succ_ne_zero m), sub_zero]

/-- **The power sums through the ordinary partial Bell polynomials.** -/
theorem power_sum_eq_ord_bell (s : Finset ι) (u : ι → A) (n : ℕ) (hn : 1 ≤ n) :
    powerSum A s u n =
      (-1 : A) ^ n * (n : A) *
        ∑ k ∈ Finset.Ico 1 (n + 1), algebraMap ℚ A (1 / k) *
          ordPartialBell (fun j => -(∑ t ∈ s.powersetCard j, ∏ i ∈ t, u i)) n k := by
  set e : ℕ → A := fun j => ∑ t ∈ s.powersetCard j, ∏ i ∈ t, u i with he
  have hkey := (coeff_logOf_elemSeries A s u n).symm.trans
    (coeff_logOf_elemSeries_ord A s u n)
  -- drop the `k = 0` term, which the logarithm kills
  have hdrop : ∑ k ∈ Finset.range (n + 1), coeff k (log A) * ordPartialBell e n k
      = ∑ k ∈ Finset.Ico 1 (n + 1), coeff k (log A) * ordPartialBell e n k := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ n + 1),
      Nat.Ico_zero_eq_range, Finset.sum_range_one, coeff_log, if_pos rfl, zero_mul, zero_add]
  -- rewrite each summand in the source's shape
  have hterm : ∀ k ∈ Finset.Ico 1 (n + 1),
      coeff k (log A) * ordPartialBell e n k
        = -(algebraMap ℚ A (1 / k) * ordPartialBell (fun j => -(e j)) n k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [coeff_log, if_neg (Nat.succ_ne_zero m),
      show (fun j => -(e j)) = (fun j => (-1 : A) * e j) by funext j; ring,
      ordPartialBell_mul_left]
    have hsign : algebraMap ℚ A ((-1 : ℚ) ^ (m + 1 + 1) / ((m + 1 : ℕ) : ℚ))
        = -(algebraMap ℚ A (1 / ((m + 1 : ℕ) : ℚ)) * (-1 : A) ^ (m + 1)) := by
      rw [show ((-1 : ℚ) ^ (m + 1 + 1) / ((m + 1 : ℕ) : ℚ))
          = (-1 : ℚ) ^ (m + 1 + 1) * (1 / ((m + 1 : ℕ) : ℚ)) by ring,
        map_mul, map_pow, map_neg, map_one, pow_succ]
      ring
    rw [hsign]
    ring
  rw [hdrop, Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hkey
  -- now solve for the power sum
  have hfac : algebraMap ℚ A (1 / n.factorial) * ((n : A) * (((n - 1).factorial : ℕ) : A))
      = 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hne : (((m + 1).factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (m + 1)
    rw [Nat.add_sub_cancel, ← Nat.cast_mul, ← Nat.factorial_succ,
      ← map_natCast (algebraMap ℚ A) (m + 1).factorial, ← map_mul,
      one_div, inv_mul_cancel₀ hne, map_one]
  rw [newtonWeight, if_neg (by omega)] at hkey
  have hpow : (-1 : A) ^ n * (-1 : A) ^ (n - 1) = -1 := by
    rw [← pow_add, show n + (n - 1) = 2 * (n - 1) + 1 by omega, pow_succ, pow_mul]
    norm_num
  calc powerSum A s u n
      = -((-1 : A) ^ n * (-1 : A) ^ (n - 1)) *
          (algebraMap ℚ A (1 / n.factorial) * ((n : A) * (((n - 1).factorial : ℕ) : A))) *
          powerSum A s u n := by rw [hpow, hfac]; ring
    _ = (-1 : A) ^ n * (n : A) *
          -(algebraMap ℚ A (1 / n.factorial) *
            ((-1 : A) ^ (n - 1) * (((n - 1).factorial : ℕ) : A) * powerSum A s u n)) := by
        ring
    _ = (-1 : A) ^ n * (n : A) *
          ∑ k ∈ Finset.Ico 1 (n + 1), algebraMap ℚ A (1 / k) *
            ordPartialBell (fun j => -(e j)) n k := by
        rw [hkey]; ring

end OrdBell

end Fabius
