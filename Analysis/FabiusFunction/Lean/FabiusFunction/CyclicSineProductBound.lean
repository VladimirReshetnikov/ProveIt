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
        rw [prod_range_succ_mod_rotate, ← prod_pow]
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

end Fabius
