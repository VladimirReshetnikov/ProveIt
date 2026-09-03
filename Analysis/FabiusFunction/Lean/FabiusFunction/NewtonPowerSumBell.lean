import FabiusFunction.ElementarySymmetricBell
import FabiusFunction.CumulantBellFormula

/-!
# Power sums from elementary symmetric functions, through the Bell polynomials

The companion of `esymm_eq_bell_complete`, and the second half of the source's
symmetric-function theorem:

`(-1)^{n-1} (n-1)! p_n = ∑_{k=1}^{n} (-1)^{k-1} (k-1)! B_{n,k}(1! e_1, 2! e_2, …)`
(`newton_power_sum`),

equivalently `p_n = ((-1)^{n-1}/(n-1)!) ∑_k …` (`power_sum_eq`).

Nothing new is proved here.  The Newton weights `(-1)^{r-1}(r-1)! p_r` have the scaled
elementary symmetric functions `n! e_n` as their complete Bell family, which is
`esymm_eq_bell_complete` read backwards; the cumulants are what a complete Bell family
determines, so the Newton weights are the cumulants of that sequence; and the cumulants have
the displayed closed form by `cumulant_eq_cumulantSum`.  The identity is the composition of
those three facts.

Stating it in the cleared form, multiplied through by `(-1)^{n-1}(n-1)!`, keeps it free of
division; `power_sum_eq` restores the source's divided form for readers who want it.

## Main results

* `newton_power_sum`, `power_sum_eq`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Newton

variable {ι : Type*} (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The scaled elementary symmetric functions `m_j = j! e_j`, which are the moments whose
cumulants are the Newton weights. -/
noncomputable def scaledElemSym (s : Finset ι) (u : ι → A) (j : ℕ) : A :=
  ((j.factorial : ℕ) : A) * ∑ t ∈ s.powersetCard j, ∏ i ∈ t, u i

theorem scaledElemSym_zero (s : Finset ι) (u : ι → A) : scaledElemSym A s u 0 = 1 := by
  rw [scaledElemSym, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty,
    Nat.factorial_zero, Nat.cast_one, mul_one]

/-- The scaled elementary symmetric functions are the complete Bell family of the Newton
weights. -/
theorem complete_newtonWeight (s : Finset ι) (u : ι → A) :
    Bell.complete (newtonWeight A s u) = scaledElemSym A s u := by
  funext j
  have hcancel : ((j.factorial : ℕ) : A) * algebraMap ℚ A (1 / j.factorial) = 1 := by
    have hn : ((j.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    rw [← map_natCast (algebraMap ℚ A) j.factorial, ← map_mul, mul_one_div_cancel hn, map_one]
  rw [scaledElemSym, esymm_eq_bell_complete A s u j, ← mul_assoc, hcancel, one_mul]

/-- **Newton's identity in Bell form:**
`(-1)^{n-1} (n-1)! p_n = ∑_{k=1}^{n} (-1)^{k-1} (k-1)! B_{n,k}(1! e_1, 2! e_2, …)`. -/
theorem newton_power_sum (s : Finset ι) (u : ι → A) (n : ℕ) (hn : 1 ≤ n) :
    (-1 : A) ^ (n - 1) * (((n - 1).factorial : ℕ) : A) * powerSum A s u n =
      ∑ k ∈ Finset.Ico 1 (n + 1), (-1 : A) ^ (k - 1) * (((k - 1).factorial : ℕ) : A) *
        partialBell (scaledElemSym A s u) n k := by
  have hk0 : newtonWeight A s u 0 = 0 := by rw [newtonWeight, if_pos rfl]
  have hcum : newtonWeight A s u = Bell.cumulant (scaledElemSym A s u) :=
    Bell.eq_cumulant_of_complete hk0 (complete_newtonWeight A s u)
  have hclosed : Bell.cumulant (scaledElemSym A s u) = cumulantSum A (scaledElemSym A s u) :=
    cumulant_eq_cumulantSum A _ (scaledElemSym_zero A s u)
  have h := congrFun (hcum.trans hclosed) n
  rw [newtonWeight, if_neg (by omega)] at h
  rw [h, cumulantSum]

/-- The source's divided form: `p_n = ((-1)^{n-1}/(n-1)!) ∑_k (-1)^{k-1}(k-1)! B_{n,k}`. -/
theorem power_sum_eq (s : Finset ι) (u : ι → A) (n : ℕ) (hn : 1 ≤ n) :
    powerSum A s u n =
      (-1 : A) ^ (n - 1) * algebraMap ℚ A (1 / (n - 1).factorial) *
        ∑ k ∈ Finset.Ico 1 (n + 1), (-1 : A) ^ (k - 1) * (((k - 1).factorial : ℕ) : A) *
          partialBell (scaledElemSym A s u) n k := by
  have hcancel : algebraMap ℚ A (1 / (n - 1).factorial) * (((n - 1).factorial : ℕ) : A) = 1 := by
    have hne : (((n - 1).factorial : ℚ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - 1)
    rw [← map_natCast (algebraMap ℚ A) (n - 1).factorial, ← map_mul, one_div,
      inv_mul_cancel₀ hne, map_one]
  have hsq : (-1 : A) ^ (n - 1) * (-1 : A) ^ (n - 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [← newton_power_sum A s u n hn]
  calc powerSum A s u n
      = (-1 : A) ^ (n - 1) * (-1 : A) ^ (n - 1) *
          (algebraMap ℚ A (1 / (n - 1).factorial) * (((n - 1).factorial : ℕ) : A)) *
          powerSum A s u n := by rw [hsq, hcancel, one_mul, one_mul]
    _ = (-1 : A) ^ (n - 1) * algebraMap ℚ A (1 / (n - 1).factorial) *
          ((-1 : A) ^ (n - 1) * (((n - 1).factorial : ℕ) : A) * powerSum A s u n) := by ring

end Newton

end Fabius
