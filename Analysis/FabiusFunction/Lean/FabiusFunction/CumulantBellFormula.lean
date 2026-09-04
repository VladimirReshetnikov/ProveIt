import FabiusFunction.ExpLog
import FabiusFunction.DiamondPower

/-!
# The cumulants in closed form

The corpus defines `Bell.cumulant` by the recurrence that inverts `Bell.complete`, and proves
the two mutually inverse.  What it did not have is the closed form,

`κ_n = ∑_{k=1}^{n} (-1)^{k-1} (k-1)! B_{n,k}(m_1, m_2, …)`   (`cumulant_eq_cumulantSum`),

which is the statement the literature calls the moment-to-cumulant formula and the one every
application actually uses.

The proof is `K = log M` made formal.  `M - 1` is the Bell weight series of the moments
(`egfA_sub_one`), so substituting it into Mathlib's `log` and expanding the substitution term
by term gives a sum over powers of that weight series, whose coefficients the corpus already
reads off as partial Bell polynomials.  That identifies `log M` as the exponential generating
function of the displayed sum (`logOf_egfA`).  Applying `exp` then returns `M`, by
`Fabius.exp_subst_logOf`, and the exponential of a Bell weight series is the generating
function of the complete Bell polynomials, so the displayed sum has `m` as its complete Bell
family — which is exactly what characterises the cumulants.

The dependency on `DiamondPower` is only for `egfA_eq_bellWeightSeries`, the observation that
a sequence vanishing at `0` has the same exponential generating function either way.  Importing
it is cheaper than proving it a second time, and a second proof under a different name is the
one kind of duplication the corpus's name audit cannot see.

## Main results

* `cumulantSum`, `cumulantSum_zero`.
* `egfA_sub_one`, `coeff_logOf_egfA`, `logOf_egfA`.
* `cumulant_eq_cumulantSum`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Cumulant

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The closed form of the cumulants:
`∑_{k=1}^{n} (-1)^{k-1} (k-1)! B_{n,k}(m)`. -/
noncomputable def cumulantSum (m : ℕ → A) (n : ℕ) : A :=
  ∑ k ∈ Finset.Ico 1 (n + 1),
    (-1 : A) ^ (k - 1) * (((k - 1).factorial : ℕ) : A) * partialBell m n k

/-- The closed-form cumulant sum vanishes in degree zero. -/
@[simp] theorem cumulantSum_zero (m : ℕ → A) : cumulantSum A m 0 = 0 := by
  rw [cumulantSum, show Finset.Ico 1 (0 + 1) = (∅ : Finset ℕ) from rfl, Finset.sum_empty]

/-- For a normalized moment sequence, `M - 1` is the Bell weight series. -/
theorem egfA_sub_one (m : ℕ → A) (h0 : m 0 = 1) :
    egfA A m - 1 = bellWeightSeries A m := by
  refine PowerSeries.ext fun n => ?_
  rw [map_sub, coeff_egfA, bellWeightSeries, coeff_egfA]
  rcases eq_or_ne n 0 with rfl | hn
  · have h1 : coeff 0 (1 : A⟦X⟧) = 1 := by rw [coeff_zero_eq_constantCoeff, map_one]
    have h2 : algebraMap ℚ A (1 / (Nat.factorial 0 : ℕ)) = 1 := by
      rw [Nat.factorial_zero, Nat.cast_one, div_one, map_one]
    rw [if_pos rfl, mul_zero, h1, h2, h0, mul_one, sub_self]
  · rw [if_neg hn, coeff_one, if_neg hn, sub_zero]

/-- The single coefficient computation behind the formula: the `d`-th log coefficient against
the `d`-th power of the weight series. -/
theorem log_coeff_mul_factorial (d : ℕ) :
    algebraMap ℚ A ((-1 : ℚ) ^ (d + 1 + 1) / ((d + 1 : ℕ) : ℚ)) *
        (((d + 1).factorial : ℕ) : A) =
      (-1 : A) ^ d * ((d.factorial : ℕ) : A) := by
  have hstep : ((-1 : ℚ) ^ (d + 1 + 1) / ((d + 1 : ℕ) : ℚ)) * ((d + 1 : ℕ) : ℚ)
      = (-1 : ℚ) ^ d := by
    have hd : ((d + 1 : ℕ) : ℚ) ≠ 0 := by
      have : (0 : ℚ) < ((d + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos d
      exact ne_of_gt this
    rw [div_mul_cancel₀ _ hd, pow_succ, pow_succ]
    ring
  calc algebraMap ℚ A ((-1 : ℚ) ^ (d + 1 + 1) / ((d + 1 : ℕ) : ℚ)) *
        (((d + 1).factorial : ℕ) : A)
      = algebraMap ℚ A ((-1 : ℚ) ^ (d + 1 + 1) / ((d + 1 : ℕ) : ℚ)) *
          (((d + 1 : ℕ) : A) * ((d.factorial : ℕ) : A)) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
    _ = (algebraMap ℚ A ((-1 : ℚ) ^ (d + 1 + 1) / ((d + 1 : ℕ) : ℚ)) * ((d + 1 : ℕ) : A)) *
          ((d.factorial : ℕ) : A) := by ring
    _ = (-1 : A) ^ d * ((d.factorial : ℕ) : A) := by
        congr 1
        rw [← map_natCast (algebraMap ℚ A) (d + 1), ← map_mul, hstep, map_pow, map_neg,
          map_one]

/-- **The logarithm of a moment generating function** has the closed-form cumulants as its
exponential coefficients. -/
theorem coeff_logOf_egfA (m : ℕ → A) (h0 : m 0 = 1) (n : ℕ) :
    coeff n (logOf (egfA A m)) = algebraMap ℚ A (1 / n.factorial) * cumulantSum A m n := by
  have hW : constantCoeff (bellWeightSeries A m) = 0 := constantCoeff_bellWeightSeries A m
  rw [logOf_eq, egfA_sub_one A m h0]
  have hexp := coeff_mul_subst_eq A hW 1 (log A) n
  rw [one_mul] at hexp
  have hterms : ∀ d ∈ Finset.range (n + 1),
      coeff d (log A) * coeff n (1 * bellWeightSeries A m ^ d)
        = if d = 0 then 0 else
            algebraMap ℚ A (1 / n.factorial) *
              ((-1 : A) ^ (d - 1) * (((d - 1).factorial : ℕ) : A) * partialBell m n d) := by
    intro d _
    rcases eq_or_ne d 0 with rfl | hd
    · rw [if_pos rfl, coeff_log, if_pos rfl, zero_mul]
    · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      rw [if_neg (Nat.succ_ne_zero e), one_mul, coeff_log, if_neg (Nat.succ_ne_zero e),
        coeff_bellWeightSeries_pow, Nat.add_sub_cancel]
      calc algebraMap ℚ A ((-1 : ℚ) ^ (e + 1 + 1) / ((e + 1 : ℕ) : ℚ)) *
            ((((e + 1).factorial : ℕ) : A) *
              (algebraMap ℚ A (1 / n.factorial) * partialBell m n (e + 1)))
          = (algebraMap ℚ A ((-1 : ℚ) ^ (e + 1 + 1) / ((e + 1 : ℕ) : ℚ)) *
              (((e + 1).factorial : ℕ) : A)) *
              (algebraMap ℚ A (1 / n.factorial) * partialBell m n (e + 1)) := by ring
        _ = algebraMap ℚ A (1 / n.factorial) *
              ((-1 : A) ^ e * ((e.factorial : ℕ) : A) * partialBell m n (e + 1)) := by
            rw [log_coeff_mul_factorial]
            ring
  rw [hexp, Finset.sum_congr rfl hterms, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ n + 1),
    Nat.Ico_zero_eq_range, Finset.sum_range_one, if_pos rfl, zero_add, cumulantSum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Ico.mp hd).1
  rw [if_neg (by omega)]

/-- `log M` is the exponential generating function of the closed-form cumulants. -/
theorem logOf_egfA (m : ℕ → A) (h0 : m 0 = 1) :
    logOf (egfA A m) = egfA A (cumulantSum A m) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_logOf_egfA A m h0, coeff_egfA]

/-- **The moment-to-cumulant formula:** the cumulants defined by the inverting recurrence are
the alternating factorial-weighted sum of partial Bell polynomials in the moments. -/
theorem cumulant_eq_cumulantSum (m : ℕ → A) (h0 : m 0 = 1) :
    Bell.cumulant m = cumulantSum A m := by
  have hc : constantCoeff (egfA A m) = 1 := by rw [constantCoeff_egfA, h0]
  have hT0 : cumulantSum A m 0 = 0 := cumulantSum_zero A m
  have hexp : (exp A).subst (logOf (egfA A m)) = egfA A m := exp_subst_logOf hc
  rw [logOf_egfA A m h0, egfA_eq_bellWeightSeries A (cumulantSum A m) hT0,
    exp_subst_bellWeightSeries] at hexp
  have hm : Bell.complete (cumulantSum A m) = m := seq_eq_of_egfA_eq A hexp
  exact (Bell.eq_cumulant_of_complete hT0 hm).symm

end Cumulant

end Fabius
