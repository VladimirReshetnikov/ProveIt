import FabiusFunction.ThueMorseSineProduct

/-!
# Gelfond's uniform upper bound

The atlas's `eq:gelfond-upper`, previously a literature citation
(Gelfond 1968): the Thue–Morse trigonometric polynomial obeys the
sharp uniform bound

`sup_x |∑_{n<2^m} ε(n)·e^(inx)| ≤ (2/√3)·3^(m/2) = 2·(√3)^(m-1)`,

so `log₄3` is the optimal uniform growth exponent of Thue–Morse
exponential sums.

The whole theorem reduces to **one one-variable inequality**: for the
factor `φ(t) = 2·|sin t|` of the sine-product magnitude,

`φ(t)²·φ(2t) ≤ 3√3`   for every real `t`,

which after squaring and substituting `u = sin²t` is the polynomial
bound `256·u³(1-u) ≤ 27` — an identity away from the sum of squares
`27 - 256u³ + 256u⁴ = (4u-3)²·((4u+1)²+2)`, tight exactly at the
Gelfond angle `u = 3/4`, i.e. `t = π/3`, the fixed cycle of angle
doubling.  Telescoping the inequality along the doubling orbit and
peeling the two boundary factors (`φ ≤ 2`) gives the cube of the
claimed bound with constant `8 = (2/√3)³·3^(3/2)`.

* `two_abs_sin_sq_mul_le` — **the Gelfond inequality**
  `φ(t)²·φ(2t) ≤ √27`.
* `gelfond_prod_le` — the telescoped product bound
  `∏_{j<m} φ(2^j·θ) ≤ 2·(√3)^(m-1)`.
* `gelfond_uniform_bound` — **the uniform exponential-sum bound**
  (`eq:gelfond-upper`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- `√27 = (√3)³`. -/
theorem sqrt_twentyseven : Real.sqrt 27 = Real.sqrt 3 ^ 3 := by
  have h : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [h, show (27 : ℝ) = 9 * 3 by norm_num,
    Real.sqrt_mul (by norm_num) 3,
    show Real.sqrt 9 = 3 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]]

/-- **The Gelfond inequality**: `(2|sin t|)²·(2|sin 2t|) ≤ √27`,
tight at `t = π/3`.  After squaring it is
`256·u³(1-u) ≤ 27` for `u = sin²t`, an exact sum of squares. -/
theorem two_abs_sin_sq_mul_le (t : ℝ) :
    (2 * |Real.sin t|) ^ 2 * (2 * |Real.sin (2 * t)|) ≤
      Real.sqrt 27 := by
  have h0 : 0 ≤ (2 * |Real.sin t|) ^ 2 * (2 * |Real.sin (2 * t)|) := by
    positivity
  rw [← Real.sqrt_sq h0]
  refine Real.sqrt_le_sqrt ?_
  have h1 : |Real.sin t| ^ 2 = Real.sin t ^ 2 := sq_abs _
  have h2 : |Real.sin (2 * t)| ^ 2 = Real.sin (2 * t) ^ 2 := sq_abs _
  rw [show ((2 * |Real.sin t|) ^ 2 * (2 * |Real.sin (2 * t)|)) ^ 2 =
      64 * (|Real.sin t| ^ 2) ^ 2 * |Real.sin (2 * t)| ^ 2 by ring,
    h1, h2]
  have hs := Real.sin_sq_add_cos_sq t
  have hc : Real.cos t ^ 2 = 1 - Real.sin t ^ 2 := by linarith
  have h2t2 : Real.sin (2 * t) ^ 2 =
      4 * Real.sin t ^ 2 * (1 - Real.sin t ^ 2) := by
    rw [Real.sin_two_mul,
      show (2 * Real.sin t * Real.cos t) ^ 2 =
        4 * Real.sin t ^ 2 * Real.cos t ^ 2 by ring, hc]
  rw [h2t2]
  have hprod : (0 : ℝ) ≤ (4 * Real.sin t ^ 2 - 3) ^ 2 *
      ((4 * Real.sin t ^ 2 + 1) ^ 2 + 2) :=
    mul_nonneg (sq_nonneg _)
      (add_nonneg (sq_nonneg _) (by norm_num))
  nlinarith [hprod]

/-- **The telescoped Gelfond product bound**: along the doubling
orbit, `∏_{j<m} 2|sin(2^j·θ)| ≤ 2·(√3)^(m-1)`. -/
theorem gelfond_prod_le (θ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∏ j ∈ range m, (2 * |Real.sin (2 ^ j * θ)|) ≤
      2 * Real.sqrt 3 ^ (m - 1) := by
  obtain ⟨K, rfl⟩ : ∃ K, m = K + 1 := ⟨m - 1, by omega⟩
  have hf0 : ∀ j : ℕ, 0 ≤ 2 * |Real.sin (2 ^ j * θ)| := fun j => by
    positivity
  have hf2 : ∀ j : ℕ, 2 * |Real.sin (2 ^ j * θ)| ≤ 2 := fun j => by
    have h := Real.abs_sin_le_one (2 ^ j * θ)
    linarith
  have hkey : ∀ j : ℕ,
      (2 * |Real.sin (2 ^ j * θ)|) ^ 2 *
        (2 * |Real.sin (2 ^ (j + 1) * θ)|) ≤ Real.sqrt 27 := by
    intro j
    have h := two_abs_sin_sq_mul_le (2 ^ j * θ)
    rwa [show 2 * (2 ^ j * θ) = 2 ^ (j + 1) * θ by ring] at h
  have hstep : ∏ j ∈ range K,
      ((2 * |Real.sin (2 ^ j * θ)|) ^ 2 *
        (2 * |Real.sin (2 ^ (j + 1) * θ)|)) ≤ Real.sqrt 27 ^ K := by
    calc ∏ j ∈ range K,
        ((2 * |Real.sin (2 ^ j * θ)|) ^ 2 *
          (2 * |Real.sin (2 ^ (j + 1) * θ)|))
        ≤ ∏ _j ∈ range K, Real.sqrt 27 :=
          Finset.prod_le_prod (fun j _ => by positivity)
            (fun j _ => hkey j)
      _ = Real.sqrt 27 ^ K := by rw [Finset.prod_const, card_range]
  have h1 : ∏ j ∈ range (K + 1), (2 * |Real.sin (2 ^ j * θ)|) =
      (∏ j ∈ range K, (2 * |Real.sin (2 ^ j * θ)|)) *
        (2 * |Real.sin (2 ^ K * θ)|) := prod_range_succ _ K
  have h2 : ∏ j ∈ range (K + 1), (2 * |Real.sin (2 ^ j * θ)|) =
      (∏ j ∈ range K, (2 * |Real.sin (2 ^ (j + 1) * θ)|)) *
        (2 * |Real.sin (2 ^ 0 * θ)|) := prod_range_succ' _ K
  have hsplit : ∏ j ∈ range K, ((2 * |Real.sin (2 ^ j * θ)|) ^ 2 *
      (2 * |Real.sin (2 ^ (j + 1) * θ)|)) =
      (∏ j ∈ range K, (2 * |Real.sin (2 ^ j * θ)|)) ^ 2 *
        ∏ j ∈ range K, (2 * |Real.sin (2 ^ (j + 1) * θ)|) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
  have hgroup : (∏ j ∈ range (K + 1),
      (2 * |Real.sin (2 ^ j * θ)|)) ^ 3 =
      (∏ j ∈ range K, ((2 * |Real.sin (2 ^ j * θ)|) ^ 2 *
        (2 * |Real.sin (2 ^ (j + 1) * θ)|))) *
        (2 * |Real.sin (2 ^ 0 * θ)|) *
        (2 * |Real.sin (2 ^ K * θ)|) ^ 2 := by
    calc (∏ j ∈ range (K + 1), (2 * |Real.sin (2 ^ j * θ)|)) ^ 3
        = ((∏ j ∈ range K, (2 * |Real.sin (2 ^ j * θ)|)) *
            (2 * |Real.sin (2 ^ K * θ)|)) ^ 2 *
            ((∏ j ∈ range K, (2 * |Real.sin (2 ^ (j + 1) * θ)|)) *
              (2 * |Real.sin (2 ^ 0 * θ)|)) := by
          rw [← h1, ← h2]
          ring
      _ = (∏ j ∈ range K, ((2 * |Real.sin (2 ^ j * θ)|) ^ 2 *
            (2 * |Real.sin (2 ^ (j + 1) * θ)|))) *
            (2 * |Real.sin (2 ^ 0 * θ)|) *
            (2 * |Real.sin (2 ^ K * θ)|) ^ 2 := by
          rw [hsplit]
          ring
  have hP3 : (∏ j ∈ range (K + 1),
      (2 * |Real.sin (2 ^ j * θ)|)) ^ 3 ≤ Real.sqrt 27 ^ K * 8 := by
    rw [hgroup]
    have hb1 := hf2 0
    have hb2 := hf2 K
    have hn1 := hf0 0
    have hn2 := hf0 K
    have c1 : (∏ j ∈ range K, ((2 * |Real.sin (2 ^ j * θ)|) ^ 2 *
        (2 * |Real.sin (2 ^ (j + 1) * θ)|))) *
        (2 * |Real.sin (2 ^ 0 * θ)|) ≤ Real.sqrt 27 ^ K * 2 :=
      mul_le_mul hstep hb1 hn1 (by positivity)
    have hsq : (2 * |Real.sin (2 ^ K * θ)|) ^ 2 ≤ 4 := by
      nlinarith [hb2, hn2]
    have c2 : (∏ j ∈ range K, ((2 * |Real.sin (2 ^ j * θ)|) ^ 2 *
        (2 * |Real.sin (2 ^ (j + 1) * θ)|))) *
        (2 * |Real.sin (2 ^ 0 * θ)|) *
        (2 * |Real.sin (2 ^ K * θ)|) ^ 2 ≤
        Real.sqrt 27 ^ K * 2 * 4 :=
      mul_le_mul c1 hsq (sq_nonneg _) (by positivity)
    linarith [c2]
  have hrhs : (2 * Real.sqrt 3 ^ K) ^ 3 = Real.sqrt 27 ^ K * 8 := by
    rw [mul_pow, ← pow_mul, sqrt_twentyseven, ← pow_mul]
    ring
  have hfinal := le_of_pow_le_pow_left₀
    (by norm_num : (3 : ℕ) ≠ 0) (by positivity) (hrhs ▸ hP3)
  simpa using hfinal

/-- **Gelfond's uniform bound** (`eq:gelfond-upper`): for every real
`x` and `m ≥ 1`,
`|∑_{n<2^m} ε(n)·e^(inx)| ≤ 2·(√3)^(m-1) = (2/√3)·3^(m/2)`. -/
theorem gelfond_uniform_bound (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ‖∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
        Complex.exp ((x : ℂ) * Complex.I) ^ n‖ ≤
      2 * Real.sqrt 3 ^ (m - 1) := by
  rw [sum_thueMorseSign_exp_eq_sin_prod x m, norm_mul, norm_mul,
    norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hnegI : ‖(-2 * Complex.I : ℂ)‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
    simp
  rw [hnegI, Complex.norm_prod]
  have hterm : ∀ j ∈ range m, ‖((Real.sin (2 ^ j * x / 2) : ℝ) : ℂ)‖ =
      |Real.sin (2 ^ j * (x / 2))| := by
    intro j _
    rw [Complex.norm_real, Real.norm_eq_abs,
      show (2 : ℝ) ^ j * x / 2 = 2 ^ j * (x / 2) by ring]
  rw [Finset.prod_congr rfl hterm]
  have hcollect : (2 : ℝ) ^ m *
      ∏ j ∈ range m, |Real.sin (2 ^ j * (x / 2))| =
      ∏ j ∈ range m, (2 * |Real.sin (2 ^ j * (x / 2))|) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, card_range]
  rw [hcollect]
  exact gelfond_prod_le (x / 2) m hm

end Fabius
