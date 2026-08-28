import FabiusFunction.SincZetaSeries
import FabiusFunction.SincCanonicalProduct

/-!
# The all-orders Euler–zeta expansion of the dyadic sinc product

The frontier drafts' `thm:all-orders-Q` (Fabius/Rvachev–Thue–Morse
frontier results, `eq:Q-all-orders`): for `|t| < π·2^(m+1)`,

`log (Q_∞(t)/Q_m(t)) = -∑_{r ≥ 1} ζ(2r)/(r π^{2r} (4^r - 1)) · t^{2r} 4^{-rm}`,

the disk being maximal.  In the repository's normalization
`Φ(z) = ∏_{h ≥ 0} sinc (πz/2ʰ) = Q_∞(2πz)`, the `m = 0` statement is
the closed exponential form of the whole product on the central disk:

`Φ(z) = exp (-∑_{r ≥ 1} ζ(2r)·4ʳ/(r (4ʳ - 1)) · z^{2r})` for `‖z‖ < 1`,

proved by one application of the Euler log transform to the *pair*
family `(z/2ʰ)²/(n+1)²` — the same engine as `lem:logsinc`, over the
product index `ℕ × ℕ`.  The scale direction contributes one geometric
sum per order (`tsum_div_two_pow_even_pow`), whose pointwise form is
the field identity `(x/2ʰ)^(2k) = x^(2k)·((4ᵏ)⁻¹)ʰ`
(`div_two_pow_even_pow`); the `n`-direction is the even zeta value
already computed for a single sinc (`sinc_family_powerSum`).  Together
they produce the Lambert-type kernel `4ʳ/(4ʳ - 1) = 1/(1 - 4^{-r})`.
The general-`m` statement follows by the already-formal dyadic shell
factorization (`rvachevFourierProduct_two_pow_mul`) applied at
`z/2^m`; no quotients are needed, and the finite prefix appears
explicitly.

* `div_two_pow_even_pow` — the dyadic scale collapse, in any field.
* `tsum_div_two_pow_even_pow` — its geometric summation.
* `sinc_pair_powerSum` — the power sums of the pair family, for
  **every** `z : ℂ` (no smallness hypothesis).
* `rvachevFourierProduct_eq_cexp` — the master exponential form on
  `‖z‖ < 1`.
* `rvachevFourierProduct_eq_prefix_mul_cexp` — `thm:all-orders-Q`:
  the exact factorization `Φ(z) = (∏_{j<m} sinc (πz/2ʲ)) ·
  exp (-∑_{r ≥ 1} ζ(2r)·4ʳ/(r(4ʳ-1)) · (z/2^m)^{2r})` on `‖z‖ < 2^m`.
-/

set_option autoImplicit false

open Complex Real Finset

namespace Fabius

/-- The norm of a complex power of two. -/
theorem norm_two_pow_complex (h : ℕ) : ‖(2 : ℂ) ^ h‖ = 2 ^ h := by
  rw [norm_pow, Complex.norm_ofNat]

/-- The norm of the shifted natural coercion `‖(n : ℂ) + 1‖ = n + 1`. -/
theorem norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast]
  push_cast
  ring

/-- Scaling into the central disk: `‖z‖ < 2^m` gives `‖z/2^m‖ < 1`. -/
theorem norm_div_two_pow_lt_one {z : ℂ} {m : ℕ} (hz : ‖z‖ < 2 ^ m) :
    ‖z / (2 : ℂ) ^ m‖ < 1 := by
  rw [norm_div, norm_two_pow_complex]
  exact (div_lt_one (by positivity)).mpr hz

/-- `4^k - 1` does not vanish in `ℂ` for `k ≥ 1`. -/
theorem four_pow_sub_one_ne_zero {k : ℕ} (hk : k ≠ 0) :
    ((4 : ℂ) ^ k - 1) ≠ 0 := by
  intro h
  have h1 : (4 : ℂ) ^ k = 1 := by
    have h' := sub_eq_zero.mp h
    simpa using h'
  have h2 : ‖(4 : ℂ) ^ k‖ = 1 := by rw [h1, norm_one]
  rw [norm_pow, Complex.norm_ofNat] at h2
  have h3 : (1 : ℝ) < 4 ^ k := one_lt_pow₀ (by norm_num) hk
  rw [h2] at h3
  exact lt_irrefl 1 h3

/-- **The dyadic scale collapse**, in any field: dividing the argument
of an even power by `2ʰ` extracts the geometric factor `((4ᵏ)⁻¹)ʰ`:
`(x/2ʰ)^(2k) = x^(2k) · ((4ᵏ)⁻¹)ʰ`. -/
theorem div_two_pow_even_pow {K : Type*} [Field K] (x : K) (h k : ℕ) :
    (x / 2 ^ h) ^ (2 * k) = x ^ (2 * k) * (((4 : K) ^ k)⁻¹) ^ h := by
  have hbase : ((2 : K) ^ h) ^ (2 * k) = ((4 : K) ^ k) ^ h := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    simp only [← pow_mul]
    congr 1
    ring
  rw [div_pow, hbase, div_eq_mul_inv, ← inv_pow]

/-- **Geometric collapse of dyadic-scale even powers**: for every
`z : ℂ` and `k ≥ 1`,
`∑'_h (z/2ʰ)^(2k) = z^(2k) · 4ᵏ/(4ᵏ - 1)`. -/
theorem tsum_div_two_pow_even_pow (z : ℂ) {k : ℕ} (hk : k ≠ 0) :
    ∑' h : ℕ, (z / 2 ^ h) ^ (2 * k) =
      z ^ (2 * k) * ((4 : ℂ) ^ k / ((4 : ℂ) ^ k - 1)) := by
  have h40 : ((4 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h41 := four_pow_sub_one_ne_zero hk
  have hlt : ‖((4 : ℂ) ^ k)⁻¹‖ < 1 := by
    rw [norm_inv, norm_pow, Complex.norm_ofNat, inv_lt_one_iff₀]
    right
    exact one_lt_pow₀ (by norm_num) hk
  calc ∑' h : ℕ, (z / 2 ^ h) ^ (2 * k)
      = ∑' h : ℕ, z ^ (2 * k) * (((4 : ℂ) ^ k)⁻¹) ^ h :=
        tsum_congr fun h => div_two_pow_even_pow z h k
    _ = z ^ (2 * k) * (1 - ((4 : ℂ) ^ k)⁻¹)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hlt]
    _ = z ^ (2 * k) * ((4 : ℂ) ^ k / ((4 : ℂ) ^ k - 1)) := by
        have hstep : (1 : ℂ) - ((4 : ℂ) ^ k)⁻¹ =
            ((4 : ℂ) ^ k - 1) / (4 : ℂ) ^ k := by
          rw [eq_div_iff h40, sub_mul, one_mul, inv_mul_cancel₀ h40]
        rw [hstep, inv_div]

/-- Norm-summability of the dyadic pair family `(z/2ʰ)²/(n+1)²` —
geometric in the scale, `p`-series in the frequency. -/
theorem sinc_pair_norm_summable (z : ℂ) :
    Summable fun p : ℕ × ℕ =>
      ‖(z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2‖ := by
  have hs1 : Summable fun h : ℕ => ‖(z / 2 ^ h) ^ 2‖ := by
    have hgeo : Summable fun h : ℕ => ‖z‖ ^ 2 * ((4 : ℝ)⁻¹) ^ h :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine hgeo.congr fun h => Eq.symm ?_
    rw [norm_pow, norm_div, norm_two_pow_complex]
    have h1 := div_two_pow_even_pow (K := ℝ) ‖z‖ h 1
    simpa using h1
  have hp2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have h := summable_one_div_add_one_pow (k := 1) one_ne_zero
    simpa using h
  have hprod := hs1.mul_of_nonneg hp2
    (fun h => norm_nonneg _) (fun n => by positivity)
  refine hprod.congr fun p => Eq.symm ?_
  rw [norm_div, norm_pow ((p.2 : ℂ) + 1) 2, norm_natCast_add_one,
    div_eq_mul_one_div]

/-- **Power sums of the dyadic pair family**, for every `z : ℂ`:

`∑'_{(h,n)} ((z/2ʰ)²/(n+1)²)^(r+1)
  = ζ(2(r+1)) · z^(2(r+1)) · 4^(r+1)/(4^(r+1) - 1)`.

The `n`-sum is the even zeta value of a single sinc
(`sinc_family_powerSum`); the `h`-sum is the geometric scale collapse.
No smallness of `z` is needed. -/
theorem sinc_pair_powerSum (z : ℂ) (r : ℕ) :
    ∑' p : ℕ × ℕ, ((z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) =
      (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) * 4 ^ (r + 1) /
        (((4 : ℂ) ^ (r + 1)) - 1) := by
  have hterm : ∀ p : ℕ × ℕ,
      ((z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) =
        ((z / 2 ^ p.1) ^ 2) ^ (r + 1) *
          (1 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) := by
    intro p
    rw [div_eq_mul_one_div, mul_pow]
  have hf : Summable fun h : ℕ => ‖((z / 2 ^ h) ^ 2) ^ (r + 1)‖ := by
    have hgeo : Summable fun h : ℕ =>
        ‖z‖ ^ (2 * (r + 1)) * (((4 : ℝ) ^ (r + 1))⁻¹) ^ h := by
      refine (summable_geometric_of_lt_one (by positivity) ?_).mul_left _
      rw [inv_lt_one_iff₀]
      right
      exact one_lt_pow₀ (by norm_num) r.succ_ne_zero
    refine hgeo.congr fun h => Eq.symm ?_
    rw [← pow_mul, norm_pow, norm_div, norm_two_pow_complex,
      div_two_pow_even_pow (K := ℝ) ‖z‖ h (r + 1)]
  have hg : Summable fun n : ℕ => ‖(1 / ((n : ℂ) + 1) ^ 2) ^ (r + 1)‖ := by
    refine (summable_one_div_add_one_pow r.succ_ne_zero).congr
      fun n => Eq.symm ?_
    rw [one_div_pow, ← pow_mul, norm_div, norm_one, norm_pow,
      norm_natCast_add_one]
  have hFsum : Summable fun p : ℕ × ℕ =>
      ((z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) := by
    refine Summable.of_norm ?_
    refine (hf.mul_of_nonneg hg (fun h => norm_nonneg _)
      (fun n => norm_nonneg _)).congr fun p => Eq.symm ?_
    rw [hterm p, norm_mul]
  have hfiber : ∀ h : ℕ, Summable fun n : ℕ =>
      ((z / 2 ^ h) ^ 2 / ((n : ℂ) + 1) ^ 2) ^ (r + 1) := by
    intro h
    have hgc : Summable fun n : ℕ => (1 / ((n : ℂ) + 1) ^ 2) ^ (r + 1) :=
      Summable.of_norm hg
    refine (hgc.mul_left (((z / 2 ^ h) ^ 2) ^ (r + 1))).congr fun n => ?_
    exact (hterm (h, n)).symm
  rw [hFsum.tsum_prod' hfiber]
  calc ∑' h : ℕ, ∑' n : ℕ, ((z / 2 ^ h) ^ 2 / ((n : ℂ) + 1) ^ 2) ^ (r + 1)
      = ∑' h : ℕ, (evenZeta (r + 1) : ℂ) * (z / 2 ^ h) ^ (2 * (r + 1)) :=
        tsum_congr fun h => sinc_family_powerSum (z / 2 ^ h) r
    _ = (evenZeta (r + 1) : ℂ) * ∑' h : ℕ, (z / 2 ^ h) ^ (2 * (r + 1)) :=
        tsum_mul_left
    _ = (evenZeta (r + 1) : ℂ) * (z ^ (2 * (r + 1)) *
          ((4 : ℂ) ^ (r + 1) / ((4 : ℂ) ^ (r + 1) - 1))) := by
        rw [tsum_div_two_pow_even_pow z r.succ_ne_zero]
    _ = (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) * 4 ^ (r + 1) /
          (((4 : ℂ) ^ (r + 1)) - 1) := by
        rw [← mul_assoc, mul_div_assoc']

/-- **The master Euler–zeta form of the dyadic sinc product**
(`eq:Q-all-orders` at `m = 0`, exponential form): on the central disk
`‖z‖ < 1`,

`Φ(z) = exp (-∑'_{r} ζ(2(r+1)) · z^(2(r+1)) · 4^(r+1) /
              ((r+1) (4^(r+1) - 1)))`.

The sum over `r : ℕ` realizes `∑_{r ≥ 1} ζ(2r) 4ʳ z^{2r} / (r (4ʳ-1))`,
and the boundary `‖z‖ = 1` carries the nearest zeros `z = ±1` of `Φ`,
so the disk is maximal. -/
theorem rvachevFourierProduct_eq_cexp {z : ℂ} (hz : ‖z‖ < 1) :
    rvachevFourierProduct z =
      Complex.exp (-∑' r : ℕ,
        (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) * 4 ^ (r + 1) /
          (((r : ℂ) + 1) * (((4 : ℂ) ^ (r + 1)) - 1))) := by
  have hlt : ∀ p : ℕ × ℕ, ‖(z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2‖ < 1 := by
    intro p
    have hzp : ‖z / (2 : ℂ) ^ p.1‖ < 1 :=
      norm_div_two_pow_lt_one (lt_of_lt_of_le hz (one_le_pow₀ (by norm_num)))
    exact sinc_family_norm_lt_one hzp p.2
  rw [rvachevFourierProduct_eq_tprod_pair,
    tprod_congr fun p : ℕ × ℕ => one_add_sineTerm_eq (z / 2 ^ p.1) p.2,
    tprod_one_sub_eq_cexp_powerSum hlt (sinc_pair_norm_summable z)]
  congr 2
  refine tsum_congr fun r => ?_
  rw [sinc_pair_powerSum, div_div,
    mul_comm (((4 : ℂ) ^ (r + 1)) - 1) ((r : ℂ) + 1)]

/-- **The all-orders sinc-tail expansion** (`thm:all-orders-Q`,
exponential form): for `‖z‖ < 2^m`, the dyadic sinc product factors
exactly into its `m`-term finite prefix and the zeta-corrected tail

`Φ(z) = (∏_{j<m} sinc (πz/2ʲ)) ·
  exp (-∑'_{r} ζ(2(r+1)) · (z/2^m)^(2(r+1)) · 4^(r+1) /
        ((r+1)(4^(r+1) - 1)))`.

In the draft's `t = 2πz` normalization this is
`Q_∞(t) = Q_m(t) · exp (-∑_{r ≥ 1} ζ(2r) t^{2r} 4^{-rm} /
(r π^{2r} (4^r - 1)))` on `|t| < π·2^(m+1)`, the disk being maximal. -/
theorem rvachevFourierProduct_eq_prefix_mul_cexp {m : ℕ} {z : ℂ}
    (hz : ‖z‖ < 2 ^ m) :
    rvachevFourierProduct z =
      (∏ j ∈ Finset.range m, complexSinc (π * (z / 2 ^ j))) *
        Complex.exp (-∑' r : ℕ,
          (evenZeta (r + 1) : ℂ) * (z / 2 ^ m) ^ (2 * (r + 1)) * 4 ^ (r + 1) /
            (((r : ℂ) + 1) * (((4 : ℂ) ^ (r + 1)) - 1))) := by
  have h2m : ((2 : ℂ) ^ m) ≠ 0 := pow_ne_zero m two_ne_zero
  have hfac := rvachevFourierProduct_two_pow_mul m (z / 2 ^ m)
  rw [mul_comm ((2 : ℂ) ^ m) (z / 2 ^ m), div_mul_cancel₀ z h2m] at hfac
  rw [hfac, rvachevFourierProduct_eq_cexp (norm_div_two_pow_lt_one hz)]
  congr 1
  have hpt : ∀ j ∈ Finset.range m,
      complexSinc (π * ((2 : ℂ) ^ (j + 1) * (z / 2 ^ m))) =
        complexSinc (π * (z / 2 ^ (m - 1 - j))) := by
    intro j hj
    have hjm : j < m := Finset.mem_range.mp hj
    have he : (j + 1) + (m - 1 - j) = m := by omega
    have harg : (2 : ℂ) ^ (j + 1) * (z / 2 ^ m) = z / 2 ^ (m - 1 - j) := by
      rw [← mul_div_assoc, div_eq_div_iff h2m (pow_ne_zero _ two_ne_zero),
        mul_comm ((2 : ℂ) ^ (j + 1)) z, mul_assoc, ← pow_add, he]
    rw [harg]
  rw [Finset.prod_congr rfl hpt]
  exact Finset.prod_range_reflect
    (fun j => complexSinc (π * (z / 2 ^ j))) m

/-- **The Fourier transform of the up-function in closed exponential
form**: for a Fabius function and `‖z‖ < 1`,

`Û(z) = exp (-∑_{r ≥ 1} ζ(2r)·4ʳ·z^{2r}/(r (4ʳ - 1)))`

— the Fourier transform of an honest compactly supported `C^∞` density
written as a single explicit elementary series, by composing the
integral-to-product identity with the master Euler–zeta form. -/
theorem rvachevFourier_eq_cexp (F : BoundedFabius) (hF : IsFabius F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    rvachevFourier F z =
      Complex.exp (-∑' r : ℕ,
        (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) * 4 ^ (r + 1) /
          (((r : ℂ) + 1) * (((4 : ℂ) ^ (r + 1)) - 1))) := by
  rw [rvachevFourier_eq_product F hF z, rvachevFourierProduct_eq_cexp hz]

end Fabius
