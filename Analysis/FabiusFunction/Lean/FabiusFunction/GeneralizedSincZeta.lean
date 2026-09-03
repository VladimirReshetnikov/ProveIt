import FabiusFunction.WeightedEulerTransform
import FabiusFunction.GeneralizedCanonicalForm
import FabiusFunction.SincZetaDyadic

/-!
# The Euler–zeta expansion of `Φ_a` at a general admissible weight

`SincZetaDyadic` proves the all-orders exponential form of the
*constant-weight* sinc product on the central disk,

`Φ(z) = exp (-∑_{r ≥ 1} ζ(2r) · 4ʳ/(r(4ʳ - 1)) · z^{2r})`,  `‖z‖ < 1`.

The exponents volume's cumulant display `p1:eq:kappaP` is the same
statement at a general weight, read probabilistically: the even
cumulants of `X_a` are `κ_{2j} = (B_{2j}/(2j)) · A_a(4^{-j})`.  Its
crosswalk records the cumulants as unformalized, "needing the
probabilistic model behind `Φ_P`".

The **analytic** half needs no model, and is proved here:

`Φ_a(z) = exp (-∑_{r ≥ 1} ζ(2r) · A_a(4^{-r}) · z^{2r} / r)`,  `‖z‖ < 1`,

where `A_a(q) = ∑_h a_h qʰ` is the volume's generating function.  This
is the cumulant statement with the random variable removed: the
coefficient of `z^{2r}` in `-log Φ_a` is `ζ(2r) A_a(4^{-r})/r`, and
what remains to connect it to `κ_{2j}(X_a)` is the identification of
`Φ_a` as a characteristic function, not any further analysis.  At
`a ≡ 1` the kernel `A_1(4^{-r}) = 4ʳ/(4ʳ - 1)` is recovered, which is
the constant-weight display.

Two ingredients make the general weight reachable.
`FabiusFunction.WeightedEulerTransform` supplies the Euler product
formula *with multiplicities*, so the exponents `a h` of the pair form
do not have to be turned into logarithms; and the scale direction
contributes `∑_h a_h (4^{-r})ʰ` in place of the geometric
`∑_h (4^{-r})ʰ`, which is exactly `A_a(4^{-r})`.

* `Fabius.weightedScaleSeries` — `A_a(4^{-k})` as a complex series;
* `Fabius.summable_weightedScaleSeries` — its convergence, from
  admissibility alone, at every `k ≥ 1`;
* `Fabius.tsum_weighted_div_two_pow_even_pow` — the weighted scale
  collapse `∑_h a_h (z/2ʰ)^{2k} = z^{2k} A_a(4^{-k})`;
* `Fabius.weighted_sinc_pair_powerSum` — **the power sums** of the
  weighted pair family;
* `Fabius.generalizedRvachevProduct_eq_cexp` — **the expansion**.
-/

set_option autoImplicit false

namespace Fabius

/-! ## The weighted scale series `A_a(4^{-k})` -/

/-- The volume's `A_a` evaluated at `4^{-k}`: `∑_h a_h (4^{-k})ʰ`. -/
noncomputable def weightedScaleSeries (a : ℕ → ℕ) (k : ℕ) : ℂ :=
  ∑' h : ℕ, (a h : ℂ) * (((4 : ℂ) ^ k)⁻¹) ^ h

/-- Admissibility alone gives convergence at every `k ≥ 1`, because
`4^{-kh} ≤ 2^{-h}` there. -/
theorem summable_weightedScaleSeries_real (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {k : ℕ} (hk : k ≠ 0) :
    Summable fun h : ℕ => (a h : ℝ) * (((4 : ℝ) ^ k)⁻¹) ^ h := by
  have h4 : (2 : ℝ) ≤ (4 : ℝ) ^ k := by
    calc (2 : ℝ) ≤ 4 := by norm_num
      _ = (4 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (4 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk)
  refine Summable.of_nonneg_of_le (fun h => by positivity) (fun h => ?_) ha
  have hle : (((4 : ℝ) ^ k)⁻¹) ^ h ≤ ((2 : ℝ)⁻¹) ^ h := by
    refine pow_le_pow_left₀ (by positivity) ?_ h
    rw [inv_le_inv₀ (by positivity) (by norm_num)]
    exact h4
  calc (a h : ℝ) * (((4 : ℝ) ^ k)⁻¹) ^ h
      ≤ (a h : ℝ) * ((2 : ℝ)⁻¹) ^ h :=
        mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
    _ = (a h : ℝ) / 2 ^ h := by
        rw [inv_pow]
        ring

/-- The complex form of the same summability. -/
theorem summable_weightedScaleSeries (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {k : ℕ} (hk : k ≠ 0) :
    Summable fun h : ℕ => (a h : ℂ) * (((4 : ℂ) ^ k)⁻¹) ^ h := by
  refine Summable.of_norm ?_
  refine (summable_weightedScaleSeries_real a ha hk).congr fun h => ?_
  rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_ofNat,
    Complex.norm_natCast]

/-- **The weighted scale collapse**: `∑_h a_h (z/2ʰ)^{2k}
= z^{2k} · A_a(4^{-k})`, the general-weight form of
`Fabius.tsum_div_two_pow_even_pow`. -/
theorem tsum_weighted_div_two_pow_even_pow (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (z : ℂ) {k : ℕ}
    (hk : k ≠ 0) :
    (∑' h : ℕ, (a h : ℂ) * (z / 2 ^ h) ^ (2 * k))
      = z ^ (2 * k) * weightedScaleSeries a k := by
  rw [weightedScaleSeries, ← tsum_mul_left]
  refine tsum_congr fun h => ?_
  rw [div_two_pow_even_pow z h k]
  ring

/-! ## The weighted pair power sums -/

/-- **The power sums of the weighted pair family**:

`∑_{(h,n)} a_h · ((z/2ʰ)²/(n+1)²)^{r+1}
   = ζ(2(r+1)) · z^{2(r+1)} · A_a(4^{-(r+1)})`.

The `n`-direction is the even zeta value of a single sinc; the
`h`-direction is the weighted scale collapse. -/
theorem weighted_sinc_pair_powerSum (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (z : ℂ) (r : ℕ) :
    (∑' p : ℕ × ℕ, (a p.1 : ℂ) *
        ((z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1))
      = (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) *
        weightedScaleSeries a (r + 1) := by
  have hterm : ∀ p : ℕ × ℕ,
      (a p.1 : ℂ) * ((z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) =
        ((a p.1 : ℂ) * ((z / 2 ^ p.1) ^ 2) ^ (r + 1)) *
          (1 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) := by
    intro p
    rw [div_eq_mul_one_div, mul_pow]
    ring
  have hf : Summable fun h : ℕ =>
      ‖(a h : ℂ) * ((z / 2 ^ h) ^ 2) ^ (r + 1)‖ := by
    refine (summable_weightedScaleSeries_real a ha
      (k := r + 1) r.succ_ne_zero).mul_left (‖z‖ ^ (2 * (r + 1)))
      |>.congr fun h => ?_
    rw [norm_mul, Complex.norm_natCast, ← pow_mul, norm_pow, norm_div,
      norm_two_pow_complex, div_two_pow_even_pow (K := ℝ) ‖z‖ h (r + 1)]
    ring
  have hg : Summable fun n : ℕ => ‖(1 / ((n : ℂ) + 1) ^ 2) ^ (r + 1)‖ := by
    refine (summable_one_div_add_one_pow r.succ_ne_zero).congr
      fun n => Eq.symm ?_
    rw [one_div_pow, ← pow_mul, norm_div, norm_one, norm_pow,
      norm_natCast_add_one]
  have hFsum : Summable fun p : ℕ × ℕ =>
      (a p.1 : ℂ) * ((z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) := by
    refine Summable.of_norm ?_
    refine (hf.mul_of_nonneg hg (fun h => norm_nonneg _)
      (fun n => norm_nonneg _)).congr fun p => Eq.symm ?_
    rw [hterm p, norm_mul]
  have hfiber : ∀ h : ℕ, Summable fun n : ℕ =>
      (a h : ℂ) * ((z / 2 ^ h) ^ 2 / ((n : ℂ) + 1) ^ 2) ^ (r + 1) := by
    intro h
    have hgc : Summable fun n : ℕ => (1 / ((n : ℂ) + 1) ^ 2) ^ (r + 1) :=
      Summable.of_norm hg
    refine (hgc.mul_left ((a h : ℂ) * ((z / 2 ^ h) ^ 2) ^ (r + 1))).congr
      fun n => ?_
    rw [← hterm (h, n)]
  rw [hFsum.tsum_prod' hfiber]
  calc ∑' h : ℕ, ∑' n : ℕ,
        (a h : ℂ) * ((z / 2 ^ h) ^ 2 / ((n : ℂ) + 1) ^ 2) ^ (r + 1)
      = ∑' h : ℕ, (a h : ℂ) *
          ((evenZeta (r + 1) : ℂ) * (z / 2 ^ h) ^ (2 * (r + 1))) :=
        tsum_congr fun h => by
          rw [tsum_mul_left, sinc_family_powerSum (z / 2 ^ h) r]
    _ = (evenZeta (r + 1) : ℂ) *
          ∑' h : ℕ, (a h : ℂ) * (z / 2 ^ h) ^ (2 * (r + 1)) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun h => by ring
    _ = (evenZeta (r + 1) : ℂ) *
          (z ^ (2 * (r + 1)) * weightedScaleSeries a (r + 1)) := by
        rw [tsum_weighted_div_two_pow_even_pow a ha z r.succ_ne_zero]
    _ = (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) *
          weightedScaleSeries a (r + 1) := by ring

/-! ## The expansion -/

/-- **The Euler–zeta expansion at a general admissible weight**: on the
central disk `‖z‖ < 1`,

`Φ_a(z) = exp (-∑'_r ζ(2(r+1)) · z^{2(r+1)} · A_a(4^{-(r+1)}) / (r+1))`.

At `a ≡ 1` this is `Fabius.rvachevFourierProduct_eq_cexp`, since
`A_1(4^{-r}) = 4ʳ/(4ʳ - 1)`.  The coefficient of `z^{2r}` in
`-log Φ_a` is `ζ(2r) A_a(4^{-r})/r`, which is the analytic content of
the volume's even-cumulant display; the probabilistic reading needs
`Φ_a` identified as a characteristic function and is not proved
here. -/
theorem generalizedRvachevProduct_eq_cexp (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) {z : ℂ}
    (hz : ‖z‖ < 1) :
    generalizedRvachevProduct a z =
      Complex.exp (-∑' r : ℕ,
        (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) *
          weightedScaleSeries a (r + 1) / ((r : ℂ) + 1)) := by
  have hlt : ∀ p : ℕ × ℕ, ‖(z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2‖ < 1 := by
    intro p
    have hzp : ‖z / (2 : ℂ) ^ p.1‖ < 1 :=
      norm_div_two_pow_lt_one (lt_of_lt_of_le hz (one_le_pow₀ (by norm_num)))
    exact sinc_family_norm_lt_one hzp p.2
  have hsum : Summable fun p : ℕ × ℕ =>
      (a p.1 : ℝ) * ‖(z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2‖ := by
    refine (summable_natCast_mul_norm_sineTerm_pair a ha z).congr fun p => ?_
    rw [sineTerm, neg_div, norm_neg]
  have hbase := tprod_one_sub_pow_eq_cexp_powerSum
    (c := fun p : ℕ × ℕ => a p.1)
    (f := fun p : ℕ × ℕ => (z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2)
    hlt hsum
  rw [generalizedRvachevProduct_eq_tprod_pair a ha z,
    tprod_congr fun p : ℕ × ℕ =>
      congrArg (fun w : ℂ => w ^ a p.1)
        (one_add_sineTerm_eq_one_sub_sq_div (z / 2 ^ p.1) p.2),
    hbase]
  congr 2
  refine tsum_congr fun r => ?_
  rw [weighted_sinc_pair_powerSum a ha z r]

end Fabius
