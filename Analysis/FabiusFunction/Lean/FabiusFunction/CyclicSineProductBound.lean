import FabiusFunction.SharpGelfondBound
import FabiusFunction.SineProductRootsUnity

/-!
# The sharp sine-product bound along a closed doubling orbit

`SharpGelfondBound` bounds a running product `∏_{j ≤ n} |sin(π 2^j t)|` by
`(√3/2)^n` — one factor short of the count, because its pairing
`s_j² · s_{j+1} ≤ (√3/2)³` runs linearly and leaves the first factor
unpaired.  When the orbit **closes**, `2^d t ≡ t (mod 1)`, the pairing can be
run cyclically, the last factor pairs with the first, and every one of the
`d` factors is covered:

`∏_{j < d} |sin(π t_j)| ≤ (√3/2)^d`.

This is the spectra volume's sharp periodic-orbit theorem `p2:thm:sqrt3-bound`,
`A_{a,q}^{1/d} ≤ √3` for `A_{a,q} = ∏_{j<d} |1 - ζ_q^{a 2^j}|` with `d` the
order of `2` modulo an odd `q`, proved here for **every** `a` and every `d`
with `2^d ≡ 1 (mod q)` (the order itself, or any multiple of it), and stated
division-free as `A_{a,q} ≤ (√3)^d`.

## Main declarations

* `prod_le_pow_of_sq_mul_succ_le_cyclic` — the cyclic pairing principle:
  if `s_j² · s_{(j+1) mod d} ≤ c³` for every `j < d`, then
  `∏_{j<d} s_j ≤ c^d`.  This is the reusable half; nothing about sines.
* `abs_prod_sin_orbit_le_sharp` — `∏_{j<d} |sin(π a 2^j / q)| ≤ (√3/2)^d`
  whenever `2^d ≡ 1 (mod q)`.
* `prod_norm_one_sub_exp_orbit_le` — **`p2:eq:sqrt3-bound`, division-free**:
  `∏_{j<d} ‖1 - e^{2πi a 2^j/q}‖ ≤ (√3)^d`.
* `prod_norm_one_sub_exp_orbit_pos` — `A_{a,q} > 0` for odd `q` coprime to `a`.
* `rational_ray_exponent_ge_min` — **`p2:eq:kappa-minimum`**, the sharp lower
  bound `κ_min` for the rational-ray exponent.

The equality case (`q = 3` only) is not proved here.
-/

set_option autoImplicit false

namespace Fabius

open Finset Real

/-! ## The cyclic pairing principle -/

/-- Rotating the index by one around `range (e+1)` permutes the factors. -/
theorem prod_range_succ_mod_rotate (s : ℕ → ℝ) (e : ℕ) :
    ∏ j ∈ range (e + 1), s ((j + 1) % (e + 1)) = ∏ j ∈ range (e + 1), s j := by
  rw [prod_range_succ, Nat.mod_self, prod_range_succ' s e]
  congr 1
  exact prod_congr rfl fun j hj => by
    rw [Nat.mod_eq_of_lt (by have := mem_range.mp hj; omega)]

/-- **Cyclic pairing.**  If every cyclically consecutive pair satisfies
`s_j² · s_{(j+1) mod d} ≤ c³`, then `∏_{j<d} s_j ≤ c^d`: cube the product,
regroup it as the product of the `d` pairs, and take cube roots. -/
theorem prod_le_pow_of_sq_mul_succ_le_cyclic {s : ℕ → ℝ} {c : ℝ} {d : ℕ} (hd : 0 < d)
    (h0 : ∀ j, 0 ≤ s j) (hc : 0 ≤ c)
    (hpair : ∀ j < d, s j ^ 2 * s ((j + 1) % d) ≤ c ^ 3) :
    ∏ j ∈ range d, s j ≤ c ^ d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  refine le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ) ≠ 0) (pow_nonneg hc _) ?_
  calc (∏ j ∈ range (e + 1), s j) ^ 3
      = (∏ j ∈ range (e + 1), s j ^ 2) * ∏ j ∈ range (e + 1), s ((j + 1) % (e + 1)) := by
        rw [prod_range_succ_mod_rotate, prod_pow]
        ring
    _ = ∏ j ∈ range (e + 1), (s j ^ 2 * s ((j + 1) % (e + 1))) := prod_mul_distrib.symm
    _ ≤ ∏ j ∈ range (e + 1), c ^ 3 :=
        prod_le_prod (fun j _ => mul_nonneg (sq_nonneg _) (h0 _))
          (fun j hj => hpair j (mem_range.mp hj))
    _ = (c ^ (e + 1)) ^ 3 := by
        rw [prod_const, card_range]
        ring

/-! ## The closed doubling orbit -/

/-- Along a closed doubling orbit, `2^d ≡ 1 (mod q)`, the factor after the
last one is the first one again: `|sin(π a 2^d / q)| = |sin(π a / q)|`. -/
theorem abs_sin_pi_mul_two_pow_div_of_mod {q d : ℕ} (hq : 0 < q) (a : ℕ)
    (hcyc : 2 ^ d % q = 1) :
    |Real.sin (π * (a * 2 ^ d / q))| = |Real.sin (π * (a / q))| := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 ^ d = q * k + 1 :=
    ⟨2 ^ d / q, by have := Nat.div_add_mod (2 ^ d) q; omega⟩
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have harg : π * (a * 2 ^ d / q) = π * (a / q) + ((a * k : ℕ) : ℝ) * π := by
    have h2 : ((2 : ℝ) ^ d) = q * k + 1 := by exact_mod_cast hk
    rw [h2]
    push_cast
    field_simp
    ring
  rw [harg, Real.sin_add_nat_mul_pi, abs_mul, abs_neg_one_pow, one_mul]

/-- **The sharp bound along a closed doubling orbit**: if `2^d ≡ 1 (mod q)`
then `∏_{j<d} |sin(π a 2^j / q)| ≤ (√3/2)^d`, with all `d` factors covered. -/
theorem abs_prod_sin_orbit_le_sharp {q d : ℕ} (hd : 0 < d) (hq : 0 < q) (a : ℕ)
    (hcyc : 2 ^ d % q = 1) :
    ∏ j ∈ range d, |Real.sin (π * (a * 2 ^ j / q))| ≤ (Real.sqrt 3 / 2) ^ d := by
  refine prod_le_pow_of_sq_mul_succ_le_cyclic hd (fun j => abs_nonneg _) (by positivity) ?_
  intro j hj
  have hpair := abs_sin_sq_mul_abs_sin_two_mul_le (π * (a * 2 ^ j / q))
  have h2 : 2 * (π * (a * 2 ^ j / q)) = π * (a * 2 ^ (j + 1) / q) := by
    rw [pow_succ]
    ring
  rw [h2] at hpair
  rcases Nat.lt_or_ge (j + 1) d with hlt | hge
  · rwa [Nat.mod_eq_of_lt hlt]
  · have hjd : j + 1 = d := by omega
    rw [hjd, Nat.mod_self]
    rw [hjd, abs_sin_pi_mul_two_pow_div_of_mod hq a hcyc] at hpair
    simpa [pow_zero, mul_one] using hpair

/-- **`p2:eq:sqrt3-bound`, division-free.**  For every `a` and every `d` with
`2^d ≡ 1 (mod q)`,

`A_{a,q} = ∏_{j<d} ‖1 - e^{2πi a 2^j/q}‖ ≤ (√3)^d`,

that is, `A_{a,q}^{1/d} ≤ √3`. -/
theorem prod_norm_one_sub_exp_orbit_le {q d : ℕ} (hd : 0 < d) (hq : 0 < q) (a : ℕ)
    (hcyc : 2 ^ d % q = 1) :
    ∏ j ∈ range d, ‖(1 : ℂ) - Complex.exp (((2 * π * (a * 2 ^ j / q) : ℝ) : ℂ) * Complex.I)‖
      ≤ Real.sqrt 3 ^ d := by
  have h := abs_prod_sin_orbit_le_sharp hd hq a hcyc
  calc ∏ j ∈ range d, ‖(1 : ℂ) - Complex.exp (((2 * π * (a * 2 ^ j / q) : ℝ) : ℂ) * Complex.I)‖
      = ∏ j ∈ range d, (2 * |Real.sin (π * (a * 2 ^ j / q))|) := by
        refine prod_congr rfl fun j _ => ?_
        rw [norm_one_sub_exp_mul_I,
          show 2 * π * (a * 2 ^ j / q) / 2 = π * (a * 2 ^ j / q) by ring]
    _ = 2 ^ d * ∏ j ∈ range d, |Real.sin (π * (a * 2 ^ j / q))| := by
        rw [prod_mul_distrib, prod_const, card_range]
    _ ≤ 2 ^ d * (Real.sqrt 3 / 2) ^ d := by gcongr
    _ = Real.sqrt 3 ^ d := by
        rw [div_pow, mul_div_cancel₀ _ (by positivity)]

/-! ## The rational-ray exponent and its sharp minimum -/

/-- A factor `1 - e^{2πi x}` vanishes only at integral `x`. -/
theorem one_sub_exp_two_pi_mul_I_ne_zero {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    (1 : ℂ) - Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have h1 : Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I) = 1 := by
    linear_combination -h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  apply hx n
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have : ((x : ℝ) : ℂ) = (n : ℂ) := by
    have h2 : ((2 * π * x : ℝ) : ℂ) * Complex.I = (n : ℂ) * (2 * π * Complex.I) := hn
    push_cast at h2
    have h3 : (x : ℂ) * (2 * π * Complex.I) = (n : ℂ) * (2 * π * Complex.I) := by
      linear_combination h2
    exact mul_right_cancel₀ (by simp [hpi, hI]) h3
  exact_mod_cast this

/-- For `q` coprime to `a 2^j`, the orbit point `a 2^j / q` is not an integer
unless `q = 1`. -/
theorem orbit_point_not_int {q a j : ℕ} (hq : 1 < q) (hcop : Nat.Coprime q (a * 2 ^ j)) :
    ∀ n : ℤ, ((a : ℝ) * 2 ^ j / q) ≠ n := by
  intro n hn
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h : ((a * 2 ^ j : ℕ) : ℝ) = (n : ℝ) * q := by
    push_cast
    rw [← hn]
    field_simp
  have hdvd : (q : ℤ) ∣ ((a * 2 ^ j : ℕ) : ℤ) := ⟨n, by exact_mod_cast h.trans (mul_comm _ _)⟩
  have hdvdN : q ∣ a * 2 ^ j := by exact_mod_cast hdvd
  have h1 : Nat.gcd q (a * 2 ^ j) = q := Nat.gcd_eq_left hdvdN
  rw [Nat.Coprime.gcd_eq_one hcop] at h1
  omega

/-- `A_{a,q} > 0`: no factor of the cycle multiplier vanishes when `q` is
coprime to `a` and odd. -/
theorem prod_norm_one_sub_exp_orbit_pos {q d a : ℕ} (hq : 1 < q) (hodd : Odd q)
    (hcop : Nat.Coprime a q) :
    0 < ∏ j ∈ range d, ‖(1 : ℂ) - Complex.exp (((2 * π * (a * 2 ^ j / q) : ℝ) : ℂ) * Complex.I)‖ := by
  refine prod_pos fun j _ => norm_pos_iff.mpr ?_
  refine one_sub_exp_two_pi_mul_I_ne_zero (orbit_point_not_int hq ?_)
  exact Nat.Coprime.mul_right hcop.symm
    (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd))

/-- **`p2:eq:kappa-minimum`.**  Writing the rational-ray exponent as
`κ_{a,q} = 1/2 + log(2π)/log 2 − log A_{a,q}/(d log 2)`, every closed
doubling orbit of an odd denominator coprime to `a` satisfies

`κ_{a,q} ≥ 1/2 + log(2π/√3)/log 2 = κ_min`. -/
theorem rational_ray_exponent_ge_min {q d a : ℕ} (hd : 0 < d) (hq : 1 < q) (hodd : Odd q)
    (hcop : Nat.Coprime a q) (hcyc : 2 ^ d % q = 1) :
    1 / 2 + Real.log (2 * π / Real.sqrt 3) / Real.log 2
      ≤ 1 / 2 + Real.log (2 * π) / Real.log 2
        - Real.log (∏ j ∈ range d,
            ‖(1 : ℂ) - Complex.exp (((2 * π * (a * 2 ^ j / q) : ℝ) : ℂ) * Complex.I)‖)
          / (d * Real.log 2) := by
  set A := ∏ j ∈ range d,
    ‖(1 : ℂ) - Complex.exp (((2 * π * (a * 2 ^ j / q) : ℝ) : ℂ) * Complex.I)‖ with hA
  have hApos : 0 < A := prod_norm_one_sub_exp_orbit_pos hq hodd hcop
  have hAle : A ≤ Real.sqrt 3 ^ d := prod_norm_one_sub_exp_orbit_le hd (by omega) a hcyc
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogA : Real.log A ≤ d * Real.log (Real.sqrt 3) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hApos hAle
  have hdiv : Real.log (2 * π / Real.sqrt 3) = Real.log (2 * π) - Real.log (Real.sqrt 3) :=
    Real.log_div (by positivity) h3.ne'
  rw [hdiv, sub_div]
  have key : Real.log A / (d * Real.log 2) ≤ Real.log (Real.sqrt 3) / Real.log 2 := by
    rw [div_le_div_iff₀ (by positivity) hlog2]
    nlinarith [hlogA, hlog2]
  linarith

/-! ## The bound is attained at `q = 3`

`abs_prod_sin_orbit_le_sharp` bounds the periodic-orbit sine product by
`(√3/2)^d`.  The volume adds that equality holds exactly when `q = 3`.  The
substantive half of that clause — that the constant cannot be lowered — is the
computation below: the orbit of `a = 1` modulo `3` has period `d = 2`, its two
points are `π/3` and `2π/3`, and the product is exactly `(√3/2)^2 = 3/4`.

The converse half, that no other odd `q` attains the bound, is not formalized. -/

/-- The two orbit points of `a = 1` modulo `3` both have `|sin| = √3/2`. -/
theorem abs_sin_orbit_three (j : ℕ) (hj : j < 2) :
    |Real.sin (π * ((1 : ℕ) * 2 ^ j / (3 : ℕ)))| = Real.sqrt 3 / 2 := by
  have hs3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  interval_cases j
  · have harg : π * (((1 : ℕ) : ℝ) * 2 ^ (0 : ℕ) / ((3 : ℕ) : ℝ)) = π / 3 := by
      push_cast
      ring
    rw [harg, Real.sin_pi_div_three, abs_of_nonneg (by positivity)]
  · have harg : π * (((1 : ℕ) : ℝ) * 2 ^ (1 : ℕ) / ((3 : ℕ) : ℝ)) = π - π / 3 := by
      push_cast
      ring
    rw [harg, Real.sin_pi_sub, Real.sin_pi_div_three, abs_of_nonneg (by positivity)]

/-- **The sharp bound is attained.**  At `q = 3`, `a = 1`, `d = 2` the
periodic-orbit sine product equals `(√3/2)^2`, so the constant `√3` of
`abs_prod_sin_orbit_le_sharp` cannot be lowered. -/
theorem abs_prod_sin_orbit_three_eq_sharp :
    ∏ j ∈ range 2, |Real.sin (π * ((1 : ℕ) * 2 ^ j / (3 : ℕ)))| = (Real.sqrt 3 / 2) ^ 2 := by
  rw [Finset.prod_congr rfl (fun j hj => abs_sin_orbit_three j (Finset.mem_range.mp hj))]
  rw [Finset.prod_const, Finset.card_range]

/-- The attained value in closed form: the product is `3/4`. -/
theorem abs_prod_sin_orbit_three_eq :
    ∏ j ∈ range 2, |Real.sin (π * ((1 : ℕ) * 2 ^ j / (3 : ℕ)))| = 3 / 4 := by
  rw [abs_prod_sin_orbit_three_eq_sharp, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

end Fabius
