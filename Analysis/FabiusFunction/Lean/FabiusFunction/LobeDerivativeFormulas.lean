import FabiusFunction.CentralLobeConcavity
import FabiusFunction.SincCanonicalProduct

/-!
# The closed derivative formulas on the central lobe

The Fourier-decay comparative audit writes the log-derivatives of
`|Φ|` as sums over the *integers* with multiplicity,

`(log|f|)'(x)  = -2x ∑_{k≥1} (1 + v₂(k)) / (k² - x²)`,
`(log|f|)''(x) = -2  ∑_{k≥1} (1 + v₂(k)) (k² + x²) / (k² - x²)²`,

and records that the log-concavity conclusion is formalized "by a
route that does not pass through" them: `CentralLobeConcavity` works
throughout with sums over the *lattice* `(h, r) ↦ 2^h (r+1)`, and the
audit notes that "the closed derivative formulas themselves are not
separately stated there".

They are here, and the gap between the two indexings is not analytic
but combinatorial — it is the same fibre equivalence
`Fabius.dyadicFactorEquiv` that turns the scale product into the
canonical product in `SincCanonicalProduct`.  The fibre of
`(h, r) ↦ 2^h (r+1)` over `k` has exactly `v₂(k) + 1` elements, and
the summand depends only on the fibre base, so the lattice sum
collapses to the integer sum with that multiplicity.

`Fabius.tsum_lobeZero_regroup` states this once for an arbitrary
summand, which is the reusable content: *any* absolutely convergent
sum over the dyadic zero lattice is the corresponding sum over the
positive integers weighted by `v₂(k) + 1`.  The two derivative
formulas are then instances, and so is anything else indexed the same
way.

* `Fabius.lobeZero_eq_succ_dyadicFactorEquiv_fst` — the bridge: the
  lattice value is the successor of its fibre base;
* `Fabius.tsum_lobeZero_regroup` — **the regrouping**;
* `Fabius.summable_central_log_deriv_term`,
  `Fabius.summable_central_log_second_deriv_term` — summability of
  the two families, both dominated by `1/lobeZero²`;
* `Fabius.tsum_central_log_deriv_eq`,
  `Fabius.tsum_central_log_second_deriv_eq` — **the audit's closed
  formulas**;
* `Fabius.hasDerivAt_central_log_series_closed` — the first formula
  as a derivative statement rather than an identity of sums.
-/

set_option autoImplicit false

namespace Fabius

/-! ## The regrouping -/

/-- The lattice value `2^h (r+1)` is the successor of the base of its
fibre under `Fabius.dyadicFactorEquiv`.  This is the only place the
two indexings are compared. -/
theorem lobeZero_eq_succ_dyadicFactorEquiv_fst (p : ℕ × ℕ) :
    lobeZero p = (((dyadicFactorEquiv p).1 + 1 : ℕ) : ℝ) := by
  have hpos : 0 < (p.2 + 1) * 2 ^ p.1 := by positivity
  have h1 : (p.2 + 1) * 2 ^ p.1 - 1 + 1 = (p.2 + 1) * 2 ^ p.1 := by omega
  rw [lobeZero]
  congr 1
  rw [dyadicFactorEquiv]
  simp only [Equiv.coe_fn_mk]
  rw [h1]
  ring

/-- **The regrouping.**  Any absolutely convergent sum over the dyadic
zero lattice is the sum over the positive integers weighted by the
fibre size `v₂(k) + 1`:

`∑_{(h,r)} g(2^h(r+1)) = ∑_{m≥0} (v₂(m+1) + 1) · g(m+1)`.

The summand depends only on the fibre base, so each fibre contributes
its size times one value.  Nothing analytic beyond the summability
hypothesis, which is what licenses the unordered regrouping. -/
theorem tsum_lobeZero_regroup {g : ℝ → ℝ}
    (hg : Summable fun p : ℕ × ℕ => g (lobeZero p)) :
    (∑' p : ℕ × ℕ, g (lobeZero p))
      = ∑' m : ℕ, ((padicValNat 2 (m + 1) + 1 : ℕ) : ℝ)
          * g (((m + 1 : ℕ) : ℝ)) := by
  classical
  set G : (Σ m : ℕ, Fin (padicValNat 2 (m + 1) + 1)) → ℝ :=
    fun s => g (((s.1 + 1 : ℕ) : ℝ)) with hG
  have hcomp : ∀ p : ℕ × ℕ, g (lobeZero p) = G (dyadicFactorEquiv p) := by
    intro p
    rw [hG, lobeZero_eq_succ_dyadicFactorEquiv_fst p]
  have hGsum : Summable G := by
    rw [← dyadicFactorEquiv.summable_iff]
    exact hg.congr hcomp
  have h1 : (∑' p : ℕ × ℕ, g (lobeZero p)) = ∑' s, G s := by
    rw [tsum_congr hcomp]
    exact dyadicFactorEquiv.tsum_eq G
  rw [h1, hGsum.tsum_sigma]
  refine tsum_congr fun m => ?_
  rw [tsum_fintype]
  simp [hG]

/-! ## Summability of the two families -/

/-- The first-derivative family is dominated by `1 / lobeZero²`: the
denominator satisfies `L² - x² ≥ L²(1 - x²)` because `L ≥ 1`. -/
theorem summable_central_log_deriv_term {x : ℝ} (hx : |x| < 1) :
    Summable fun p : ℕ × ℕ =>
      -(2 * x) / ((lobeZero p) ^ 2 - x ^ 2) := by
  have hx2 : x ^ 2 < 1 := by
    have := abs_lt.mp hx
    nlinarith
  have h1x : (0 : ℝ) < 1 - x ^ 2 := by linarith
  have hbound : ∀ p : ℕ × ℕ,
      ‖-(2 * x) / ((lobeZero p) ^ 2 - x ^ 2)‖
        ≤ (2 * |x| / (1 - x ^ 2)) * (1 / (lobeZero p) ^ 2) := by
    intro p
    have hL : (1 : ℝ) ≤ (lobeZero p) ^ 2 := one_le_sq_lobeZero p
    have hL0 : (0 : ℝ) < (lobeZero p) ^ 2 := pow_pos (lobeZero_pos p) 2
    have hden : (lobeZero p) ^ 2 * (1 - x ^ 2)
        ≤ (lobeZero p) ^ 2 - x ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < (lobeZero p) ^ 2 * (1 - x ^ 2) := by positivity
    have hnorm : ‖-(2 * x) / ((lobeZero p) ^ 2 - x ^ 2)‖
        = 2 * |x| / ((lobeZero p) ^ 2 - x ^ 2) := by
      rw [norm_div, norm_neg, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_pos (lt_of_lt_of_le hpos hden)]
    have hmono : 2 * |x| / ((lobeZero p) ^ 2 - x ^ 2)
        ≤ 2 * |x| / ((lobeZero p) ^ 2 * (1 - x ^ 2)) :=
      div_le_div_of_nonneg_left (by positivity) hpos hden
    have hval : 2 * |x| / ((lobeZero p) ^ 2 * (1 - x ^ 2))
        = (2 * |x| / (1 - x ^ 2)) * (1 / (lobeZero p) ^ 2) := by
      field_simp
    rw [hnorm, ← hval]
    exact hmono
  exact Summable.of_norm_bounded
    (summable_inv_sq_lobeZero.mul_left _) hbound

/-- The second-derivative family is dominated the same way: `L² + x²
≤ 2L²` and `(L² - x²)² ≥ (L²(1 - x²))²`. -/
theorem summable_central_log_second_deriv_term {x : ℝ} (hx : |x| < 1) :
    Summable fun p : ℕ × ℕ =>
      -(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2 := by
  have hx2 : x ^ 2 < 1 := by
    have := abs_lt.mp hx
    nlinarith
  have h1x : (0 : ℝ) < 1 - x ^ 2 := by linarith
  have hbound : ∀ p : ℕ × ℕ,
      ‖-(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
          ((lobeZero p) ^ 2 - x ^ 2) ^ 2‖
        ≤ (4 / (1 - x ^ 2) ^ 2) * (1 / (lobeZero p) ^ 2) := by
    intro p
    have hL : (1 : ℝ) ≤ (lobeZero p) ^ 2 := one_le_sq_lobeZero p
    have hL0 : (0 : ℝ) < (lobeZero p) ^ 2 := pow_pos (lobeZero_pos p) 2
    have hd : (lobeZero p) ^ 2 * (1 - x ^ 2)
        ≤ (lobeZero p) ^ 2 - x ^ 2 := by nlinarith
    have hdpos : (0 : ℝ) < (lobeZero p) ^ 2 * (1 - x ^ 2) := by positivity
    have hsqpos : (0 : ℝ) < ((lobeZero p) ^ 2 * (1 - x ^ 2)) ^ 2 := by
      positivity
    have hsq : ((lobeZero p) ^ 2 * (1 - x ^ 2)) ^ 2
        ≤ ((lobeZero p) ^ 2 - x ^ 2) ^ 2 := by nlinarith
    have hnum : (0 : ℝ) < 2 * ((lobeZero p) ^ 2 + x ^ 2) := by positivity
    have hnorm : ‖-(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
          ((lobeZero p) ^ 2 - x ^ 2) ^ 2‖
        = 2 * ((lobeZero p) ^ 2 + x ^ 2) /
          ((lobeZero p) ^ 2 - x ^ 2) ^ 2 := by
      rw [norm_div, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hnum, abs_of_pos (lt_of_lt_of_le hsqpos hsq)]
    have hstep1 : 2 * ((lobeZero p) ^ 2 + x ^ 2) /
          ((lobeZero p) ^ 2 - x ^ 2) ^ 2
        ≤ 4 * (lobeZero p) ^ 2 /
          ((lobeZero p) ^ 2 * (1 - x ^ 2)) ^ 2 := by
      refine div_le_div₀ (by positivity) (by nlinarith) hsqpos hsq
    have hval : 4 * (lobeZero p) ^ 2 /
          ((lobeZero p) ^ 2 * (1 - x ^ 2)) ^ 2
        = (4 / (1 - x ^ 2) ^ 2) * (1 / (lobeZero p) ^ 2) := by
      field_simp
    rw [hnorm, ← hval]
    exact hstep1
  exact Summable.of_norm_bounded
    (summable_inv_sq_lobeZero.mul_left _) hbound

/-! ## The audit's closed formulas -/

/-- **The first closed formula.**

`∑_{(h,r)} -(2x)/((2^h(r+1))² - x²)
   = ∑_{m≥0} (v₂(m+1)+1) · (-(2x)/((m+1)² - x²))`,

which is the audit's `-2x ∑_{k≥1} (1 + v₂(k))/(k² - x²)` with
`k = m+1`. -/
theorem tsum_central_log_deriv_eq {x : ℝ} (hx : |x| < 1) :
    (∑' p : ℕ × ℕ, -(2 * x) / ((lobeZero p) ^ 2 - x ^ 2))
      = ∑' m : ℕ, ((padicValNat 2 (m + 1) + 1 : ℕ) : ℝ) *
          (-(2 * x) / ((((m + 1 : ℕ) : ℝ)) ^ 2 - x ^ 2)) :=
  tsum_lobeZero_regroup (g := fun t => -(2 * x) / (t ^ 2 - x ^ 2))
    (summable_central_log_deriv_term hx)

/-- **The second closed formula**, the audit's
`-2 ∑_{k≥1} (1 + v₂(k))(k² + x²)/(k² - x²)²`. -/
theorem tsum_central_log_second_deriv_eq {x : ℝ} (hx : |x| < 1) :
    (∑' p : ℕ × ℕ, -(2 * ((lobeZero p) ^ 2 + x ^ 2)) /
        ((lobeZero p) ^ 2 - x ^ 2) ^ 2)
      = ∑' m : ℕ, ((padicValNat 2 (m + 1) + 1 : ℕ) : ℝ) *
          (-(2 * ((((m + 1 : ℕ) : ℝ)) ^ 2 + x ^ 2)) /
            ((((m + 1 : ℕ) : ℝ)) ^ 2 - x ^ 2) ^ 2) :=
  tsum_lobeZero_regroup
    (g := fun t => -(2 * (t ^ 2 + x ^ 2)) / (t ^ 2 - x ^ 2) ^ 2)
    (summable_central_log_second_deriv_term hx)

/-- The first formula as a derivative statement: the log-series has
derivative the audit's integer-indexed sum. -/
theorem hasDerivAt_central_log_series_closed {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun z => ∑' p : ℕ × ℕ,
        Real.log (1 - z ^ 2 / (lobeZero p) ^ 2))
      (∑' m : ℕ, ((padicValNat 2 (m + 1) + 1 : ℕ) : ℝ) *
        (-(2 * x) / ((((m + 1 : ℕ) : ℝ)) ^ 2 - x ^ 2))) x := by
  have h := hasDerivAt_central_log_series hx
  rwa [tsum_central_log_deriv_eq hx] at h

end Fabius
