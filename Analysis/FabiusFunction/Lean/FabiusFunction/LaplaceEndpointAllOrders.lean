import FabiusFunction.SincZetaDyadic
import FabiusFunction.NegativeLaplaceVertical
import FabiusFunction.EvenZetaValues
import FabiusFunction.ThueMorseBooleanCube
import FabiusFunction.BaseDigitProuhet

/-!
# The endpoint Laplace product to all orders

The atlas's endpoint Laplace product is
`G(-s) = ∏_{k ≥ 1} (1 - e^{-s/2^k}) / (s/2^k)`, which the corpus knows as the
half-moment generating function `complexGeneratingFunction F (-s)`
(`complexGeneratingFunction_neg_eq_tprod`).  Three results of the atlas's
Part 2 are proved here from the dyadic Euler–zeta engine:

* **`p2:thm:G-all-orders`**: on `|u| < 4π`,
  `G(-u) = exp (-u/2 + ∑_{r≥1} B_{2r} u^{2r} / (2 r (2r)! (4^r - 1)))`.
  It is the master zeta form of the sinc product
  (`rvachevFourierProduct_eq_cexp`) read through the Fourier–Laplace
  rotation `G(-s) = e^{-s/2} Φ(is/(4π))` and the Bernoulli evaluation of
  `ζ(2r)`; the radius `4π` is the image of the sinc product's unit disk.
* **`p2:eq:full-G-TM`**: for `s ≠ 0` and `m ≥ 0`,
  `G(-s) = 2^{m(m+1)/2} s^{-m} P_m(e^{-s/2^m}) G(-s/2^m)` with
  `P_m(x) = ∑_{n<2^m} ε_n x^n` the finite Thue–Morse polynomial: the first
  `m` Laplace factors are a finite Thue–Morse product in disguise.
* **`p2:thm:G-TM-all`**: the two combined, on `|s/2^m| < 4π`.

## Main declarations

* `complexGeneratingFunction_neg_eq_cexp_zeta` — `G(-u)` in zeta form.
* `zeta_term_eq_bernoulli_term` — the per-term Bernoulli evaluation.
* `complexGeneratingFunction_neg_eq_cexp_bernoulli` — **`p2:thm:G-all-orders`**.
* `prod_negativeLaplaceDyadicFactor_eq_thueMorse` — the finite prefix as
  `2^{m(m+1)/2} s^{-m} P_m(e^{-s/2^m})`.
* `complexGeneratingFunction_neg_eq_thueMorse_mul` — **`p2:eq:full-G-TM`**.
* `complexGeneratingFunction_neg_eq_thueMorse_mul_cexp` — **`p2:thm:G-TM-all`**.
-/

set_option autoImplicit false

namespace Fabius

open Real Finset

/-! ## The zeta form -/

/-- **`G(-u)` in zeta form.**  On `‖u‖ < 4π`,

`G(-u) = exp (-u/2 - ∑'_r ζ(2(r+1)) (i(-u)/(4π))^(2(r+1)) 4^(r+1) / ((r+1)(4^(r+1)-1)))`. -/
theorem complexGeneratingFunction_neg_eq_cexp_zeta (F : BoundedFabius) (hF : IsFabius F)
    {u : ℂ} (hu : ‖u‖ < 4 * π) :
    complexGeneratingFunction F (-u) =
      Complex.exp (-(u / 2) - ∑' r : ℕ,
        (evenZeta (r + 1) : ℂ) * (Complex.I * (-u) / (4 * π)) ^ (2 * (r + 1)) * 4 ^ (r + 1) /
          (((r : ℂ) + 1) * (((4 : ℂ) ^ (r + 1)) - 1))) := by
  have hz : ‖Complex.I * (-u) / (4 * (π : ℂ))‖ < 1 := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, norm_neg, norm_mul,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_lt_one (by positivity)]
    exact hu
  rw [complexGeneratingFunction_eq_fourier_analytic F hF, rvachevFourier_eq_product F hF,
    rvachevFourierProduct_eq_cexp hz, ← Complex.exp_add]
  congr 1
  ring

/-! ## The Bernoulli evaluation -/

/-- The `r`-th term of the zeta series at the rotated argument equals the
`r`-th Bernoulli term of `p2:eq:G-all-orders`:

`-ζ(2k) (i(-u)/(4π))^{2k} 4^k / (k(4^k-1)) = B_{2k} u^{2k} / (2k (2k)! (4^k-1))`, `k = r+1`. -/
theorem zeta_term_eq_bernoulli_term (u : ℂ) (r : ℕ) :
    -((evenZeta (r + 1) : ℂ) * (Complex.I * (-u) / (4 * π)) ^ (2 * (r + 1)) * 4 ^ (r + 1) /
        (((r : ℂ) + 1) * (((4 : ℂ) ^ (r + 1)) - 1)))
      = ((bernoulli (2 * (r + 1)) : ℚ) : ℂ) * u ^ (2 * (r + 1)) /
          (2 * ((r : ℂ) + 1) * ((2 * (r + 1)).factorial : ℂ) * (((4 : ℂ) ^ (r + 1)) - 1)) := by
  set e : ℂ := (-1 : ℂ) ^ (r + 1) with he
  have he2 : e * e = 1 := by
    rw [he, ← pow_add, ← two_mul, pow_mul]
    norm_num
  have hζ : (evenZeta (r + 1) : ℂ)
      = -e * 2 ^ (2 * (r + 1) - 1) * (π : ℂ) ^ (2 * (r + 1)) *
          ((bernoulli (2 * (r + 1)) : ℚ) : ℂ) / ((2 * (r + 1)).factorial : ℂ) := by
    rw [evenZeta_eq_bernoulli r.succ_ne_zero]
    push_cast
    rw [he, pow_succ]
    ring
  have hI : (Complex.I * (-u) / (4 * (π : ℂ))) ^ (2 * (r + 1))
      = e * u ^ (2 * (r + 1)) / ((4 : ℂ) ^ (r + 1) * 4 ^ (r + 1) * (π : ℂ) ^ (2 * (r + 1))) := by
    rw [div_pow, mul_pow, pow_mul, Complex.I_sq, (even_two_mul _).neg_pow, mul_pow, pow_mul, he]
    ring
  have h2 : (2 : ℂ) ^ (2 * (r + 1) - 1) * 2 = 4 ^ (r + 1) := by
    rw [← pow_succ, show 2 * (r + 1) - 1 + 1 = 2 * (r + 1) by omega, pow_mul]
    norm_num
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : ((4 : ℂ) ^ (r + 1)) - 1 ≠ 0 := four_pow_sub_one_ne_zero r.succ_ne_zero
  have h4' : (4 : ℂ) ^ (r + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hf : ((2 * (r + 1)).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hr : ((r : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero r
  rw [hζ, hI, ← h2]
  have h2' : (2 : ℂ) ^ (2 * (r + 1) - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  linear_combination
    (2 * (2 : ℂ) ^ (2 * (r + 1) - 1) * (π : ℂ) ^ (2 * (r + 1)) *
      ((bernoulli (2 * (r + 1)) : ℚ) : ℂ) * u ^ (2 * (r + 1)) * ((r : ℂ) + 1) *
      ((2 * (r + 1)).factorial : ℂ) * ((2 : ℂ) ^ (2 * (r + 1) - 1) * 2 - 1) *
      (2 : ℂ) ^ (2 * (r + 1) - 1) * 2 * (2 : ℂ) ^ (2 * (r + 1) - 1) * 2) * he2

/-- **`p2:thm:G-all-orders`.**  On `‖u‖ < 4π`,

`G(-u) = exp (-u/2 + ∑'_r B_{2(r+1)} u^{2(r+1)} / (2 (r+1) (2(r+1))! (4^{r+1} - 1)))`. -/
theorem complexGeneratingFunction_neg_eq_cexp_bernoulli (F : BoundedFabius) (hF : IsFabius F)
    {u : ℂ} (hu : ‖u‖ < 4 * π) :
    complexGeneratingFunction F (-u) =
      Complex.exp (-(u / 2) + ∑' r : ℕ,
        ((bernoulli (2 * (r + 1)) : ℚ) : ℂ) * u ^ (2 * (r + 1)) /
          (2 * ((r : ℂ) + 1) * ((2 * (r + 1)).factorial : ℂ) * (((4 : ℂ) ^ (r + 1)) - 1))) := by
  rw [complexGeneratingFunction_neg_eq_cexp_zeta F hF hu, sub_eq_add_neg, ← tsum_neg]
  congr 2
  exact tsum_congr fun r => zeta_term_eq_bernoulli_term u r

/-! ## The finite Thue–Morse prefix -/

/-- Away from `s = 0`, the `n`-th dyadic Laplace factor is
`2^{n+1} (1 - e^{-s/2^{n+1}}) / s`. -/
theorem negativeLaplaceDyadicFactor_eq {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    negativeLaplaceDyadicFactor s n =
      (2 : ℂ) ^ (n + 1) / s * (1 - Complex.exp (-(s / 2 ^ (n + 1)))) := by
  have h2 : ((2 : ℂ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hne : -(s / (2 : ℂ) ^ (n + 1)) ≠ 0 := by
    rw [neg_ne_zero]
    exact div_ne_zero hs h2
  unfold negativeLaplaceDyadicFactor negativeLaplaceComplexFactor complexExpm1Div
  rw [if_neg hne]
  field_simp
  ring

/-- `∑_{n<m} (n+1) = m(m+1)/2`. -/
theorem sum_range_add_one_eq (m : ℕ) : ∑ n ∈ range m, (n + 1) = m * (m + 1) / 2 := by
  rw [← sum_range_succ_id_eq m, sum_range_succ' (fun i => i) m]
  simp

/-- **The finite prefix is a Thue–Morse polynomial**: for `s ≠ 0`,

`∏_{n<m} (1 - e^{-s/2^{n+1}})/(s/2^{n+1}) = 2^{m(m+1)/2} s^{-m} ∑_{n<2^m} ε_n e^{-ns/2^m}`. -/
theorem prod_negativeLaplaceDyadicFactor_eq_thueMorse {s : ℂ} (hs : s ≠ 0) (m : ℕ) :
    ∏ n ∈ range m, negativeLaplaceDyadicFactor s n =
      (2 : ℂ) ^ (m * (m + 1) / 2) / s ^ m *
        ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) * Complex.exp (-(s / 2 ^ m)) ^ n := by
  rw [prod_congr rfl fun n _ => negativeLaplaceDyadicFactor_eq hs n, prod_mul_distrib,
    prod_div_distrib, prod_const, card_range, prod_pow_eq_pow_sum, sum_range_add_one_eq,
    ← prod_one_sub_pow_eq_sum_thueMorseSign]
  congr 1
  -- the exponentials `e^{-s/2^{n+1}}` are the powers `x^{2^{m-1-n}}` of `x = e^{-s/2^m}`
  have hpt : ∀ n ∈ range m,
      (1 - Complex.exp (-(s / 2 ^ (n + 1)))) =
        1 - Complex.exp (-(s / 2 ^ m)) ^ (2 ^ (m - 1 - n)) := by
    intro n hn
    have hnm : n < m := mem_range.mp hn
    have he : (n + 1) + (m - 1 - n) = m := by omega
    rw [← Complex.exp_nat_mul]
    congr 2
    have h2n : ((2 : ℂ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2m : ((2 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [← he, pow_add]
    push_cast
    field_simp
    ring
  rw [prod_congr rfl hpt]
  exact (prod_range_reflect (fun j => 1 - Complex.exp (-(s / 2 ^ m)) ^ (2 ^ j)) m).symm

/-- **`p2:eq:full-G-TM`**: for `s ≠ 0`,

`G(-s) = 2^{m(m+1)/2} s^{-m} P_m(e^{-s/2^m}) · G(-s/2^m)`. -/
theorem complexGeneratingFunction_neg_eq_thueMorse_mul (F : BoundedFabius) (hF : IsFabius F)
    {s : ℂ} (hs : s ≠ 0) (m : ℕ) :
    complexGeneratingFunction F (-s) =
      (2 : ℂ) ^ (m * (m + 1) / 2) / s ^ m *
        (∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) * Complex.exp (-(s / 2 ^ m)) ^ n) *
        complexGeneratingFunction F (-(s / 2 ^ m)) := by
  rw [complexGeneratingFunction_neg_finite_refinement F hF s m,
    prod_negativeLaplaceDyadicFactor_eq_thueMorse hs m]

/-- **`p2:thm:G-TM-all`**: for `s ≠ 0` and `‖s/2^m‖ < 4π`, with `u = s/2^m`,

`G(-s) = 2^{m(m+1)/2} s^{-m} P_m(e^{-u}) ·
  exp (-u/2 + ∑'_r B_{2(r+1)} u^{2(r+1)} / (2 (r+1) (2(r+1))! (4^{r+1}-1)))`. -/
theorem complexGeneratingFunction_neg_eq_thueMorse_mul_cexp (F : BoundedFabius)
    (hF : IsFabius F) {s : ℂ} (hs : s ≠ 0) {m : ℕ} (hu : ‖s / 2 ^ m‖ < 4 * π) :
    complexGeneratingFunction F (-s) =
      (2 : ℂ) ^ (m * (m + 1) / 2) / s ^ m *
        (∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) * Complex.exp (-(s / 2 ^ m)) ^ n) *
        Complex.exp (-((s / 2 ^ m) / 2) + ∑' r : ℕ,
          ((bernoulli (2 * (r + 1)) : ℚ) : ℂ) * (s / 2 ^ m) ^ (2 * (r + 1)) /
            (2 * ((r : ℂ) + 1) * ((2 * (r + 1)).factorial : ℂ) * (((4 : ℂ) ^ (r + 1)) - 1))) := by
  rw [complexGeneratingFunction_neg_eq_thueMorse_mul F hF hs m,
    complexGeneratingFunction_neg_eq_cexp_bernoulli F hF hu]

end Fabius
