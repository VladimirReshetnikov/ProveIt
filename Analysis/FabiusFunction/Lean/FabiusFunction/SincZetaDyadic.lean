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
product index `ℕ × ℕ`.  Its power sums factor into a geometric sum in
`h` and an even zeta value in `n`, producing the Lambert-type kernel
`4ʳ/(4ʳ - 1) = 1/(1 - 4^{-r})`.  The general-`m` statement follows by
the already-formal dyadic shell factorization
(`rvachevFourierProduct_two_pow_mul`) applied at `z/2^m`; no quotients
are needed, and the finite prefix appears explicitly.

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

/-- Scaling into the central disk: `‖z‖ < 2^m` gives `‖z/2^m‖ < 1`. -/
theorem norm_div_two_pow_lt_one {z : ℂ} {m : ℕ} (hz : ‖z‖ < 2 ^ m) :
    ‖z / (2 : ℂ) ^ m‖ < 1 := by
  rw [norm_div, norm_two_pow_complex]
  exact (div_lt_one (by positivity)).mpr hz

/-- `4^(r+1) - 1` does not vanish in `ℂ`. -/
theorem four_pow_succ_sub_one_ne_zero (r : ℕ) :
    ((4 : ℂ) ^ (r + 1) - 1) ≠ 0 := by
  intro h
  have h1 : (4 : ℂ) ^ (r + 1) = 1 := by
    have h' := sub_eq_zero.mp h
    simpa using h'
  have h2 : ‖(4 : ℂ) ^ (r + 1)‖ = 1 := by rw [h1, norm_one]
  rw [norm_pow, Complex.norm_ofNat] at h2
  have h3 : (1 : ℝ) < 4 ^ (r + 1) :=
    one_lt_pow₀ (by norm_num) r.succ_ne_zero
  rw [h2] at h3
  exact lt_irrefl 1 h3

/-- **Power sums of the dyadic pair family**, for every `z : ℂ`:

`∑'_{(h,n)} ((z/2ʰ)²/(n+1)²)^(r+1)
  = ζ(2(r+1)) · z^(2(r+1)) · 4^(r+1)/(4^(r+1) - 1)`.

The geometric sum over the scale `h` produces the Lambert kernel
`1/(1 - 4^{-(r+1)})`; the sum over `n` is the even zeta value.  No
smallness of `z` is needed: each fixed power is absolutely summable
over the pair index. -/
theorem sinc_pair_powerSum (z : ℂ) (r : ℕ) :
    ∑' p : ℕ × ℕ, ((z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) =
      (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) * 4 ^ (r + 1) /
        (((4 : ℂ) ^ (r + 1)) - 1) := by
  have hinv : ‖((4 : ℂ) ^ (r + 1))⁻¹‖ < 1 := by
    rw [norm_inv, norm_pow, Complex.norm_ofNat, inv_lt_one_iff₀]
    right
    exact one_lt_pow₀ (by norm_num) r.succ_ne_zero
  have hf : Summable fun h : ℕ => ‖(((4 : ℂ) ^ (r + 1))⁻¹) ^ h‖ := by
    have hgeo : Summable fun h : ℕ => ‖((4 : ℂ) ^ (r + 1))⁻¹‖ ^ h :=
      summable_geometric_of_lt_one (norm_nonneg _) hinv
    exact hgeo.congr fun h => (norm_pow _ h).symm
  have hg : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ (2 * (r + 1))‖ := by
    refine (summable_one_div_add_one_pow r.succ_ne_zero).congr fun n => ?_
    rw [norm_div, norm_one, norm_pow,
      show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast
    ring
  have hfg := tsum_mul_tsum_of_summable_norm hf hg
  have hterm : ∀ p : ℕ × ℕ,
      ((z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1) =
        z ^ (2 * (r + 1)) *
          ((((4 : ℂ) ^ (r + 1))⁻¹) ^ p.1 *
            (1 / ((p.2 : ℂ) + 1) ^ (2 * (r + 1)))) := by
    rintro ⟨h, n⟩
    have hn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    rw [show (4 : ℂ) = 2 ^ 2 by norm_num]
    field_simp
    ring
  have h40 : ((4 : ℂ) ^ (r + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h41 := four_pow_succ_sub_one_ne_zero r
  calc ∑' p : ℕ × ℕ, ((z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) ^ (r + 1)
      = ∑' p : ℕ × ℕ, z ^ (2 * (r + 1)) *
          ((((4 : ℂ) ^ (r + 1))⁻¹) ^ p.1 *
            (1 / ((p.2 : ℂ) + 1) ^ (2 * (r + 1)))) := tsum_congr hterm
    _ = z ^ (2 * (r + 1)) * ∑' p : ℕ × ℕ,
          ((((4 : ℂ) ^ (r + 1))⁻¹) ^ p.1 *
            (1 / ((p.2 : ℂ) + 1) ^ (2 * (r + 1)))) := tsum_mul_left
    _ = z ^ (2 * (r + 1)) *
          ((∑' h : ℕ, (((4 : ℂ) ^ (r + 1))⁻¹) ^ h) *
            ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (2 * (r + 1))) := by rw [hfg]
    _ = z ^ (2 * (r + 1)) *
          ((1 - ((4 : ℂ) ^ (r + 1))⁻¹)⁻¹ * (evenZeta (r + 1) : ℂ)) := by
        rw [tsum_geometric_of_norm_lt_one hinv, ← ofReal_evenZeta]
    _ = (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) * 4 ^ (r + 1) /
          (((4 : ℂ) ^ (r + 1)) - 1) := by
        field_simp [h40, h41]
        ring

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
  have hsum : Summable fun p : ℕ × ℕ =>
      ‖(z / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2‖ := by
    have hgeo : Summable fun h : ℕ => ‖z‖ ^ 2 * ((1 : ℝ) / 4) ^ h :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hp : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * 1) :=
      summable_one_div_add_one_pow one_ne_zero
    have hprod := hgeo.mul_of_nonneg hp
      (fun h => by positivity) (fun n => by positivity)
    refine hprod.congr fun p => ?_
    rw [norm_div, norm_pow, norm_pow, norm_div, norm_two_pow_complex,
      show ((p.2 : ℂ) + 1) = ((p.2 + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    have h2 : ((2 : ℝ) ^ p.1) ≠ 0 := by positivity
    have hn : ((p.2 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    push_cast
    field_simp
    ring
  rw [rvachevFourierProduct_eq_tprod_pair,
    tprod_congr fun p : ℕ × ℕ => one_add_sineTerm_eq (z / 2 ^ p.1) p.2,
    tprod_one_sub_eq_cexp_powerSum hlt hsum]
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

end Fabius
