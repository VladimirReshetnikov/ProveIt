import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Small-divisor tree product bound

This file proves the arithmetic core of the exceptionally-small-divisor section of
`docs/surcomplex/dynamics-and-normal-forms/article.tex`: `dyn:esm:eq:sine`,
`dyn:esm:lem:cluster`, `dyn:esm:lem:packing`, `dyn:esm:thm:treebound` and
`dyn:esm:cor:chain` (i), together with the constant `C_a` of `dyn:esm:eq:Ca` built from the
rate `τ` of `dyn:esm:eq:rate`.

For `λ = e^{2πiθ}` the small divisors are `𝔡_n = |λ^n - 1|` (`smallDivisor`), and
`‖x‖_ℤ = |x - round x|` is the distance to the nearest integer (`distZ`).

* `smallDivisor_eq`: `𝔡_n = 2 sin(π ‖nθ‖_ℤ)`; `four_mul_distZ_le` and `smallDivisor_le` are
  the two halves `4 ‖nθ‖_ℤ ≤ 𝔡_n ≤ 2π ‖nθ‖_ℤ` of `dyn:esm:eq:sine`.
* `cluster` (`dyn:esm:lem:cluster`): all integers `s ∈ [1, n]` with `‖sθ‖_ℤ < 1/(4n)` are
  multiples `k q_*` of the denominator of one reduced fraction `p_*/q_*`, with nearest integers
  `k p_*`, `‖sθ‖_ℤ = k ‖q_* θ‖_ℤ` and `𝔡_s ≥ 𝔡_{q_*}`.
* Finite rooted forests are the inductive type `Forest` (left-child right-sibling encoding),
  with total weight `total`, number of vertices `card` and the list `sums` of subtree sums
  `s_v`, one per vertex. `Forest.packing` and `Forest.packing_finset`
  (`dyn:esm:lem:packing`): with positive weights, `q |A| ≤ n` for every vertex set `A` whose
  subtree sums are divisible by `q`.
* `tree_product_bound` (`dyn:esm:thm:treebound`): `∏_v 𝔡_{s_v}⁻¹ ≤ (Cn)^m e^{an}` for every
  `C ≥ 1`, `a ≥ 0` with `𝔡_s⁻¹ ≤ C e^{as}` (`s ≥ 1`). `chain_bound` is
  `dyn:esm:cor:chain` (i) in the same form. Both rest on `prod_le_of_packing`, the marking
  argument for any list of integers in `[1, n]` that satisfies the packing inequality.
* `rate` is `τ = limsup log⁺(𝔡_n⁻¹)/n` in `EReal` and `constC θ a` is
  `C_a = max(1, sup_{s ≥ 1} e^{-as} 𝔡_s⁻¹)`. For `a > τ` the supremum is finite and
  `𝔡_s⁻¹ ≤ C_a e^{as}` (`inv_smallDivisor_le_constC`), and `a > 0`. So
  `tree_product_bound_of_rate_lt` and `chain_bound_of_rate_lt` are the source statements
  with the source constant.

Apart from `smallDivisor_pos`, no result assumes irrationality of `θ`. For irrational `θ`
every `𝔡_n`, `n ≥ 1`, is positive (`smallDivisor_pos`), so the inverses and `rate` are the
source's. For rational `θ = p/q` the source has `τ = ∞`, while `𝔡_{kq} = 0` and Lean's
convention `0⁻¹ = 0` make `rate θ` finite (in fact `0`, which is not proved here), so these
statements are true but uninformative, with zero factors wherever `q ∣ s_v`. The empty
forest is allowed; it satisfies the bound trivially. A vertex set is encoded as a set of
positions in the list `sums`, which has exactly one entry per vertex (`Forest.length_sums`).

Pending: `dyn:esm:cor:chain` (ii), the fixed-complexity rate
`limsup log⁺ A_m(n)/n = τ` for the maximal tree and chain products.
-/

namespace Surreal.SmallDivisorTree

open Real

noncomputable section

/-! ### Small divisors and the distance to the nearest integer -/

/-- The distance `‖x‖_ℤ = |x - round x|` from a real number to the nearest integer. -/
def distZ (x : ℝ) : ℝ := |x - round x|

/-- `‖x‖_ℤ ≥ 0`. -/
theorem distZ_nonneg (x : ℝ) : 0 ≤ distZ x := abs_nonneg _

/-- `‖x‖_ℤ ≤ 1/2`. -/
theorem distZ_le_half (x : ℝ) : distZ x ≤ 1 / 2 := abs_sub_round x

/-- If `x` lies within `1/2` of an integer `p`, then `p` is the nearest integer to `x`. -/
theorem round_eq_and_distZ_eq {x : ℝ} {p : ℤ} (h : |x - p| < 1 / 2) :
    round x = p ∧ distZ x = |x - p| := by
  have hr : round x = p := by
    rw [round_eq_iff]
    obtain ⟨h1, h2⟩ := abs_lt.1 h
    constructor <;> linarith
  exact ⟨hr, by rw [distZ, hr]⟩

/-- The small divisor `𝔡_n = |λ^n - 1|` of `dyn:esm:eq:rate`, for `λ = e^{2πiθ}`. -/
def smallDivisor (θ : ℝ) (n : ℕ) : ℝ :=
  ‖Complex.exp (2 * π * Complex.I * θ) ^ n - 1‖

/-- `𝔡_n ≥ 0`. -/
theorem smallDivisor_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ smallDivisor θ n := norm_nonneg _

/-- `|e^{2πinθ} - 1| = 2 sin (π ‖nθ‖_ℤ)`. -/
theorem smallDivisor_eq (θ : ℝ) (n : ℕ) :
    smallDivisor θ n = 2 * Real.sin (π * distZ (n * θ)) := by
  have h1 : Complex.exp (2 * π * Complex.I * θ) ^ n =
      Complex.exp (Complex.I * ((2 * π * (n * θ) : ℝ) : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have key : |Real.sin (2 * π * (n * θ) / 2)| = Real.sin (π * distZ (n * θ)) := by
    have hx : 2 * π * (n * θ) / 2 = π * (n * θ - round ((n : ℝ) * θ)) +
        (round ((n : ℝ) * θ) : ℤ) * π := by ring
    have hle : |π * (n * θ - round ((n : ℝ) * θ))| ≤ π := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      have := abs_sub_round ((n : ℝ) * θ)
      nlinarith [Real.pi_pos]
    rw [hx, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul,
      Real.abs_sin_eq_sin_abs_of_abs_le_pi hle, abs_mul, abs_of_pos Real.pi_pos]
    rfl
  rw [smallDivisor, h1, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_two, key]

/-- Lower half of `dyn:esm:eq:sine`: `4 ‖nθ‖_ℤ ≤ 𝔡_n`. -/
theorem four_mul_distZ_le (θ : ℝ) (n : ℕ) : 4 * distZ (n * θ) ≤ smallDivisor θ n := by
  rw [smallDivisor_eq]
  have h0 := distZ_nonneg (n * θ)
  have h1 := distZ_le_half (n * θ)
  have hs := Real.mul_le_sin (x := π * distZ (n * θ)) (by positivity)
    (by nlinarith [Real.pi_pos])
  have hπ : 2 / π * (π * distZ (n * θ)) = 2 * distZ (n * θ) := by
    rw [← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero]
  linarith

/-- Upper half of `dyn:esm:eq:sine`: `𝔡_n ≤ 2π ‖nθ‖_ℤ`. -/
theorem smallDivisor_le (θ : ℝ) (n : ℕ) : smallDivisor θ n ≤ 2 * π * distZ (n * θ) := by
  rw [smallDivisor_eq]
  have := Real.sin_le (x := π * distZ (n * θ)) (by have := distZ_nonneg (n * θ); positivity)
  linarith

/-- `𝔡` is monotone in the distance to the nearest integer. -/
theorem smallDivisor_le_smallDivisor {θ : ℝ} {m n : ℕ} (h : distZ (m * θ) ≤ distZ (n * θ)) :
    smallDivisor θ m ≤ smallDivisor θ n := by
  rw [smallDivisor_eq, smallDivisor_eq]
  have h0 := distZ_nonneg (m * θ)
  have h1 := distZ_le_half (n * θ)
  have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π * distZ (m * θ))
    (y := π * distZ (n * θ)) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])
  linarith

/-- For irrational `θ` every small divisor `𝔡_n`, `n ≥ 1`, is positive. -/
theorem smallDivisor_pos {θ : ℝ} (hθ : Irrational θ) {n : ℕ} (hn : 1 ≤ n) :
    0 < smallDivisor θ n := by
  have hd : 0 < distZ (n * θ) := by
    rw [distZ, abs_pos, sub_ne_zero]
    exact (hθ.natCast_mul (by omega)).ne_int _
  linarith [four_mul_distZ_le θ n]

/-! ### One rational cluster -/

/-- If `s, t ≤ n` and `‖tθ‖_ℤ < 1/(4n)`, then `s ‖tθ‖_ℤ < 1/4`. -/
theorem natCast_mul_distZ_lt {θ : ℝ} {n s t : ℕ} (hs : s ≤ n)
    (ht : distZ (t * θ) < 1 / (4 * n)) : (s : ℝ) * distZ (t * θ) < 1 / 4 := by
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have := distZ_nonneg (t * θ)
      simp at ht
      linarith
    · exact_mod_cast h
  have h1 : distZ (t * θ) * (4 * n) < 1 := (lt_div_iff₀ (by positivity)).1 ht
  have h2 : (s : ℝ) * distZ (t * θ) ≤ n * distZ (t * θ) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (distZ_nonneg _)
  linarith

/-- The determinant step of `dyn:esm:lem:cluster`: two marked integers `s, s'` have
proportional nearest-integer numerators, `p_s s' = p_{s'} s`. -/
theorem round_mul_eq_round_mul {θ : ℝ} {n s s' : ℕ} (hs : s ≤ n) (hs' : s' ≤ n)
    (ms : distZ (s * θ) < 1 / (4 * n)) (ms' : distZ (s' * θ) < 1 / (4 * n)) :
    round ((s : ℝ) * θ) * (s' : ℤ) = round ((s' : ℝ) * θ) * (s : ℤ) := by
  rw [← sub_eq_zero, ← Int.abs_lt_one_iff, ← Int.cast_lt (R := ℝ), Int.cast_abs]
  push_cast
  have e : (round ((s : ℝ) * θ) : ℝ) * s' - round ((s' : ℝ) * θ) * s =
      s * (s' * θ - round ((s' : ℝ) * θ)) - s' * (s * θ - round ((s : ℝ) * θ)) := by ring
  have h1 := natCast_mul_distZ_lt hs ms'
  have h2 := natCast_mul_distZ_lt hs' ms
  rw [e]
  calc |(s : ℝ) * (s' * θ - round ((s' : ℝ) * θ)) - s' * (s * θ - round ((s : ℝ) * θ))|
      ≤ |(s : ℝ) * (s' * θ - round ((s' : ℝ) * θ))| + |s' * (s * θ - round ((s : ℝ) * θ))| :=
        abs_sub _ _
    _ = s * distZ (s' * θ) + s' * distZ (s * θ) := by
        rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast, distZ, distZ]
    _ < 1 := by linarith

/-- `dyn:esm:lem:cluster` (one rational cluster). Let `n ≥ 1` and call `s ∈ {1, …, n}`
*marked* when `‖sθ‖_ℤ < 1/(4n)`. If some `s₀` is marked, there is a reduced fraction `p/q`
with `1 ≤ q ≤ n`, whose numerator is the nearest integer to `qθ` and with
`‖qθ‖_ℤ < 1/(4n)`, such that every marked `s` is a multiple `s = kq`, `k ≥ 1`, the nearest
integer to `sθ` is `kp`, `‖sθ‖_ℤ = k ‖qθ‖_ℤ`, and `𝔡_q ≤ 𝔡_s`. No irrationality is needed. -/
theorem cluster (θ : ℝ) {n s₀ : ℕ} (h₀ : 1 ≤ s₀) (h₀n : s₀ ≤ n)
    (h₀θ : distZ (s₀ * θ) < 1 / (4 * n)) :
    ∃ (p : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ n ∧ Nat.Coprime p.natAbs q ∧ round ((q : ℝ) * θ) = p ∧
      distZ (q * θ) < 1 / (4 * n) ∧
      ∀ s : ℕ, 1 ≤ s → s ≤ n → distZ (s * θ) < 1 / (4 * n) →
        ∃ k : ℕ, 1 ≤ k ∧ s = k * q ∧ round ((s : ℝ) * θ) = k * p ∧
          distZ (s * θ) = k * distZ (q * θ) ∧ smallDivisor θ q ≤ smallDivisor θ s := by
  set r : ℚ := (round ((s₀ : ℝ) * θ) : ℚ) / ((s₀ : ℤ) : ℚ) with hr
  -- every marked `s` is `c * r.den` with numerator `c * r.num`
  have decomp : ∀ s : ℕ, 1 ≤ s → s ≤ n → distZ (s * θ) < 1 / (4 * n) →
      ∃ k : ℕ, 1 ≤ k ∧ s = k * r.den ∧ round ((s : ℝ) * θ) = k * r.num := by
    intro s hs1 hsn hs
    have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
    obtain ⟨c, hc1, hc2⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den
      (round ((s : ℝ) * θ)) hs0
    have hrs : ((round ((s : ℝ) * θ) : ℚ) / ((s : ℤ) : ℚ)) = r := by
      have hcross := round_mul_eq_round_mul hsn h₀n hs h₀θ
      have hs0' : ((s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hs0
      have hs₀' : ((s₀ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (show s₀ ≠ 0 by omega)
      rw [hr, div_eq_div_iff hs0' hs₀']
      exact_mod_cast hcross
    rw [hrs] at hc1 hc2
    have hden : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
    have hcpos : 0 < c := by
      by_contra hc
      have : c * (r.den : ℤ) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hden.le
      omega
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hcpos.le
    refine ⟨k, by omega, by exact_mod_cast hc2, hc1⟩
  obtain ⟨k₀, hk₀, hs₀k, hp₀k⟩ := decomp s₀ h₀ h₀n h₀θ
  have hq1 : 1 ≤ r.den := r.den_pos
  have hqn : r.den ≤ n := by
    have : r.den ≤ s₀ := by rw [hs₀k]; exact Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- `|qθ - p| = ‖s₀θ‖_ℤ / k₀ < 1/(4n)`
  have hk₀' : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
  have habs : (k₀ : ℝ) * |(r.den : ℝ) * θ - r.num| = distZ (s₀ * θ) := by
    have e : (s₀ : ℝ) * θ - round ((s₀ : ℝ) * θ) = k₀ * ((r.den : ℝ) * θ - r.num) := by
      rw [hp₀k, hs₀k]
      push_cast
      ring
    rw [distZ, e, abs_mul, Nat.abs_cast]
  have hlt : |(r.den : ℝ) * θ - r.num| < 1 / (4 * n) := by
    have h0 := abs_nonneg ((r.den : ℝ) * θ - r.num)
    nlinarith
  have hquarter : |(r.den : ℝ) * θ - r.num| < 1 / 2 := by
    have := natCast_mul_distZ_lt (s := 1) (t := s₀) (θ := θ) (by omega) h₀θ
    have h0 := abs_nonneg ((r.den : ℝ) * θ - r.num)
    push_cast at this
    nlinarith
  obtain ⟨hround, hdist⟩ := round_eq_and_distZ_eq hquarter
  refine ⟨r.num, r.den, hq1, hqn, r.reduced, hround, by rw [hdist]; exact hlt, ?_⟩
  intro s hs1 hsn hs
  obtain ⟨k, hk, hsk, hpk⟩ := decomp s hs1 hsn hs
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsd : distZ (s * θ) = k * distZ (r.den * θ) := by
    have e : (s : ℝ) * θ - round ((s : ℝ) * θ) = k * ((r.den : ℝ) * θ - r.num) := by
      rw [hpk, hsk]
      push_cast
      ring
    rw [hdist, distZ, e, abs_mul, Nat.abs_cast]
  refine ⟨k, hk, hsk, hpk, hsd, smallDivisor_le_smallDivisor ?_⟩
  rw [hsd]
  exact le_mul_of_one_le_left (distZ_nonneg _) hk'

/-! ### The marking argument -/

/-- A list product whose factors are nonnegative, at most `B e^c` on the elements satisfying
`P` and at most `B` on the others, is at most `B^{length} e^{c · #P}`. -/
theorem prod_le_pow_mul_exp_countP (f : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P] {B c : ℝ}
    (hB : 0 ≤ B) : ∀ L : List ℕ, (∀ s ∈ L, 0 ≤ f s) →
      (∀ s ∈ L, P s → f s ≤ B * Real.exp c) → (∀ s ∈ L, ¬ P s → f s ≤ B) →
      (L.map f).prod ≤ B ^ L.length * Real.exp (c * L.countP (fun s => P s))
  | [], _, _, _ => by simp
  | s :: L, h0, hP, hnP => by
    have ih := prod_le_pow_mul_exp_countP f P hB L
      (fun t ht => h0 t (List.mem_cons_of_mem _ ht))
      (fun t ht => hP t (List.mem_cons_of_mem _ ht))
      (fun t ht => hnP t (List.mem_cons_of_mem _ ht))
    have hprod : 0 ≤ (L.map f).prod := List.prod_nonneg fun x hx => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      exact h0 t (List.mem_cons_of_mem _ ht)
    rw [List.map_cons, List.prod_cons, List.length_cons, List.countP_cons, pow_succ]
    by_cases hs : P s
    · have h1 := hP s List.mem_cons_self hs
      simp only [hs, decide_true, if_true, Nat.cast_add, Nat.cast_one]
      calc f s * (L.map f).prod
          ≤ (B * Real.exp c) * (B ^ L.length * Real.exp (c * L.countP (fun s => P s))) :=
            mul_le_mul h1 ih hprod (by positivity)
        _ = _ := by rw [mul_add, mul_one, Real.exp_add]; ring
    · have h1 := hnP s List.mem_cons_self hs
      simp only [hs, decide_false, Bool.false_eq_true, if_false, add_zero]
      calc f s * (L.map f).prod
          ≤ B * (B ^ L.length * Real.exp (c * L.countP (fun s => P s))) :=
            mul_le_mul h1 ih hprod hB
        _ = _ := by ring

/-- The marking argument of `dyn:esm:thm:treebound`, abstracted from forests. Let `L` be a
list of integers in `[1, n]` such that `q · #{s ∈ L : q ∣ s} ≤ n` for every `q ≥ 1` (the
conclusion of `dyn:esm:lem:packing`), and let `C ≥ 1`, `a ≥ 0` with `𝔡_s⁻¹ ≤ C e^{as}` for
all `s ≥ 1`. Then any factors `0 ≤ f(s) ≤ max(1, 𝔡_s⁻¹)` multiply to at most `(Cn)^m e^{an}`,
`m` the length of `L`. -/
theorem prod_le_of_packing (θ : ℝ) {a C : ℝ} (ha : 0 ≤ a) (hC : 1 ≤ C)
    (hCa : ∀ s : ℕ, 1 ≤ s → (smallDivisor θ s)⁻¹ ≤ C * Real.exp (a * s))
    (f : ℕ → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hf : ∀ s, f s ≤ max 1 (smallDivisor θ s)⁻¹)
    {n : ℕ} (L : List ℕ) (hL : ∀ s ∈ L, 1 ≤ s ∧ s ≤ n)
    (hpack : ∀ q : ℕ, 1 ≤ q → q * L.countP (fun s => q ∣ s) ≤ n) :
    (L.map f).prod ≤ (C * n) ^ L.length * Real.exp (a * n) := by
  have hn1 : ∀ s ∈ L, (1 : ℝ) ≤ n := fun s hs => by
    exact_mod_cast (hL s hs).1.trans (hL s hs).2
  have hCn : 0 ≤ C * n := by positivity
  -- an unmarked factor is at most `n ≤ C n`
  have unmarked : ∀ s ∈ L, ¬ distZ (s * θ) < 1 / (4 * n) → f s ≤ C * n := by
    intro s hs hPs
    have hn := hn1 s hs
    have hd : 1 / (n : ℝ) ≤ smallDivisor θ s := by
      have h4 := four_mul_distZ_le θ s
      have h5 : 1 / (4 * n) ≤ distZ (s * θ) := not_lt.1 hPs
      have h6 : 4 * (1 / (4 * (n : ℝ))) = 1 / n := by field_simp
      linarith
    have hinv : (smallDivisor θ s)⁻¹ ≤ n := by
      calc (smallDivisor θ s)⁻¹ ≤ (1 / (n : ℝ))⁻¹ := inv_anti₀ (by positivity) hd
        _ = n := by rw [one_div, inv_inv]
    calc f s ≤ max 1 (smallDivisor θ s)⁻¹ := hf s
      _ ≤ n := max_le hn hinv
      _ ≤ C * n := le_mul_of_one_le_left (by linarith) hC
  by_cases hM : ∃ s ∈ L, distZ (s * θ) < 1 / (4 * n)
  · obtain ⟨s₀, hs₀L, hs₀⟩ := hM
    obtain ⟨p, q, hq1, -, -, -, -, hcl⟩ := cluster θ (hL s₀ hs₀L).1 (hL s₀ hs₀L).2 hs₀
    have hn : (1 : ℝ) ≤ n := hn1 s₀ hs₀L
    -- a marked factor is at most `𝔡_q⁻¹ ≤ C e^{aq}`
    have marked : ∀ s ∈ L, distZ (s * θ) < 1 / (4 * n) → f s ≤ C * n * Real.exp (a * q) := by
      intro s hs hPs
      obtain ⟨k, -, -, -, hdist, hmono⟩ := hcl s (hL s hs).1 (hL s hs).2 hPs
      have hinv : (smallDivisor θ s)⁻¹ ≤ C * Real.exp (a * q) := by
        rcases (smallDivisor_nonneg θ q).eq_or_lt with h0 | hpos
        · have hq0 : distZ (q * θ) = 0 := by
            have := four_mul_distZ_le θ q
            have := distZ_nonneg ((q : ℝ) * θ)
            linarith
          have hs0 : smallDivisor θ s = 0 := by
            have := smallDivisor_le θ s
            rw [hdist, hq0, mul_zero, mul_zero] at this
            exact le_antisymm this (smallDivisor_nonneg θ s)
          rw [hs0, inv_zero]
          positivity
        · exact (inv_anti₀ hpos hmono).trans (hCa q hq1)
      have h1 : (1 : ℝ) ≤ C * Real.exp (a * q) :=
        one_le_mul_of_one_le_of_one_le hC (Real.one_le_exp (by positivity))
      calc f s ≤ max 1 (smallDivisor θ s)⁻¹ := hf s
        _ ≤ C * Real.exp (a * q) := max_le h1 hinv
        _ ≤ C * n * Real.exp (a * q) := by
          rw [mul_right_comm]
          exact le_mul_of_one_le_right (by positivity) hn
    -- the marked vertices are multiples of `q`, so packing bounds their number
    have hcount : L.countP (fun s : ℕ => distZ ((s : ℝ) * θ) < 1 / (4 * n)) ≤
        L.countP (fun s => q ∣ s) := by
      apply List.countP_mono_left
      intro s hs hPs
      simp only [decide_eq_true_eq] at hPs ⊢
      obtain ⟨k, -, hsk, -⟩ := hcl s (hL s hs).1 (hL s hs).2 hPs
      exact ⟨k, by rw [hsk, mul_comm]⟩
    have hqM : (q : ℝ) * L.countP (fun s : ℕ => distZ ((s : ℝ) * θ) < 1 / (4 * n)) ≤ n := by
      exact_mod_cast (Nat.mul_le_mul_left q hcount).trans (hpack q hq1)
    calc (L.map f).prod ≤ (C * n) ^ L.length *
          Real.exp (a * q * L.countP (fun s : ℕ => distZ ((s : ℝ) * θ) < 1 / (4 * n))) :=
          prod_le_pow_mul_exp_countP f _ hCn L (fun s _ => hf0 s) marked unmarked
      _ ≤ (C * n) ^ L.length * Real.exp (a * n) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hqM ha
  · push Not at hM
    calc (L.map f).prod ≤ (C * n) ^ L.length *
          Real.exp (0 * L.countP (fun s : ℕ => distZ ((s : ℝ) * θ) < 1 / (4 * n))) :=
          prod_le_pow_mul_exp_countP f _ hCn L (fun s _ => hf0 s)
            (fun s hs hPs => absurd hPs (not_lt.2 (hM s hs))) unmarked
      _ ≤ (C * n) ^ L.length * Real.exp (a * n) := by
          rw [zero_mul, Real.exp_zero]
          gcongr
          exact Real.one_le_exp (by positivity)

/-! ### Rooted forests and divisible-subtree packing -/

/-- Finite rooted plane forests with vertex weights in `ℕ`, in the left-child right-sibling
encoding: `node w c r` is the forest whose first tree has a root of weight `w` with the trees
of `c` as its subtrees, followed by the remaining trees `r`. Every finite rooted forest is
represented, after ordering the roots and the children of each vertex. -/
inductive Forest : Type
  | nil : Forest
  | node (w : ℕ) (children rest : Forest) : Forest

namespace Forest

/-- The total weight `n` of a forest. -/
def total : Forest → ℕ
  | nil => 0
  | node w c r => w + c.total + r.total

/-- The number `m` of vertices of a forest. -/
def card : Forest → ℕ
  | nil => 0
  | node _ c r => c.card + r.card + 1

/-- The subtree sums `s_v` of all vertices, one entry per vertex. The subtree of a vertex
contains the vertex, so the root of the first tree has subtree sum `w + total c`. -/
def sums : Forest → List ℕ
  | nil => []
  | node w c r => (w + c.total) :: (c.sums ++ r.sums)

/-- All vertex weights are positive. -/
def PosWeights : Forest → Prop
  | nil => True
  | node w c r => 0 < w ∧ c.PosWeights ∧ r.PosWeights

/-- There is one subtree sum per vertex. -/
theorem length_sums : ∀ F : Forest, F.sums.length = F.card
  | nil => rfl
  | node _ c r => by
    simp only [sums, card, List.length_cons, List.length_append, length_sums c, length_sums r]

/-- With positive weights every subtree sum lies in `[1, n]`. -/
theorem mem_sums : ∀ F : Forest, F.PosWeights → ∀ s ∈ F.sums, 1 ≤ s ∧ s ≤ F.total
  | nil, _, s, hs => by simp [sums] at hs
  | node w c r, ⟨hw, hc, hr⟩, s, hs => by
    simp only [sums, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · simp only [total]
      omega
    · have := mem_sums c hc s hs
      simp only [total]
      omega
    · have := mem_sums r hr s hs
      simp only [total]
      omega

/-- `dyn:esm:lem:packing` (divisible-subtree packing), counting form: for a forest with
positive weights and total weight `n`, and any `q`, the number of vertices whose subtree sum is
divisible by `q` is at most `n / q`, i.e. `q · #{v : q ∣ s_v} ≤ n`. -/
theorem packing (q : ℕ) : ∀ F : Forest, F.PosWeights →
    q * F.sums.countP (fun s => q ∣ s) ≤ F.total
  | nil, _ => by simp [sums, total]
  | node w c r, ⟨hw, hc, hr⟩ => by
    have ihc := packing q c hc
    have ihr := packing q r hr
    simp only [sums, total, List.countP_cons, List.countP_append]
    by_cases hd : q ∣ w + c.total
    · obtain ⟨j, hj⟩ := id hd
      have hlt : q * c.sums.countP (fun s => q ∣ s) < q * j := by omega
      have hle : c.sums.countP (fun s => q ∣ s) + 1 ≤ j := Nat.lt_of_mul_lt_mul_left hlt
      have hmul := Nat.mul_le_mul_left q hle
      simp only [hd, decide_true, if_true]
      rw [Nat.mul_add, Nat.mul_add] at *
      omega
    · simp only [hd, decide_false, Bool.false_eq_true, if_false, add_zero]
      rw [Nat.mul_add]
      omega

/-- `dyn:esm:lem:packing` for vertex sets: for a forest with positive weights and total
weight `n`, if every vertex of `A` (vertices indexed by their position in `F.sums`, one per
vertex by `length_sums`) has subtree sum divisible by `q`, then `q |A| ≤ n`. Positivity of
the weights is needed (`dyn:esm:warn:zero`). -/
theorem packing_finset (q : ℕ) (F : Forest) (hF : F.PosWeights)
    (A : Finset (Fin F.sums.length)) (hA : ∀ v ∈ A, q ∣ F.sums.get v) :
    q * A.card ≤ F.total := by
  refine le_trans (Nat.mul_le_mul_left q ?_) (packing q F hF)
  calc A.card ≤ (Finset.univ.filter fun v : Fin F.sums.length => q ∣ F.sums.get v).card :=
        Finset.card_le_card fun v hv => Finset.mem_filter.2 ⟨Finset.mem_univ _, hA v hv⟩
    _ = F.sums.countP (fun s => q ∣ s) := by
        rw [Finset.card_def, Finset.filter_val,
          ← Multiset.countP_map F.sums.get Finset.univ.val (fun s => q ∣ s),
          Fin.univ_val_map, List.ofFn_get, Multiset.coe_countP]

end Forest

/-- `dyn:esm:thm:treebound` (tree product bound), with the constant as a hypothesis: if
`a ≥ 0`, `C ≥ 1` and `𝔡_s⁻¹ ≤ C e^{as}` for all `s ≥ 1`, then for every finite rooted forest
with positive integer weights, `m` vertices and total weight `n`,
`∏_v 𝔡_{s_v}⁻¹ ≤ (Cn)^m e^{an}`. -/
theorem tree_product_bound (θ : ℝ) {a C : ℝ} (ha : 0 ≤ a) (hC : 1 ≤ C)
    (hCa : ∀ s : ℕ, 1 ≤ s → (smallDivisor θ s)⁻¹ ≤ C * Real.exp (a * s))
    (F : Forest) (hF : F.PosWeights) :
    (F.sums.map fun s => (smallDivisor θ s)⁻¹).prod ≤
      (C * F.total) ^ F.card * Real.exp (a * F.total) := by
  rw [← F.length_sums]
  exact prod_le_of_packing θ ha hC hCa _ (fun s => inv_nonneg.2 (smallDivisor_nonneg θ s))
    (fun _ => le_max_right _ _) F.sums (F.mem_sums hF) (fun q _ => F.packing q hF)

/-! ### Strict chains -/

/-- Packing for strict chains: a strictly increasing list in `[1, n]` contains at most `n / q`
multiples of `q`. -/
theorem chain_packing (q : ℕ) {n : ℕ} (L : List ℕ) (hL : L.Pairwise (· < ·))
    (hLn : ∀ s ∈ L, 1 ≤ s ∧ s ≤ n) : q * L.countP (fun s => q ∣ s) ≤ n := by
  have hnd : (L.filter fun s => q ∣ s).Nodup := hL.nodup.filter _
  have hsub : (L.filter fun s => q ∣ s).toFinset ⊆ (Finset.Ioc 0 n).filter (q ∣ ·) := by
    intro s hs
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hs
    have := hLn s hs.1
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, this.2⟩, hs.2⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Nat.Ioc_filter_dvd_card_eq_div] at hcard
  rw [List.countP_eq_length_filter]
  calc q * (L.filter fun s => q ∣ s).length ≤ q * (n / q) := Nat.mul_le_mul_left q hcard
    _ ≤ n := Nat.mul_div_le n q

/-- `dyn:esm:cor:chain` (i), with the constant as a hypothesis: every strictly increasing
chain `1 ≤ k_1 < ⋯ < k_r ≤ n` satisfies `∏_j max(1, 𝔡_{k_j}⁻¹) ≤ (Cn)^r e^{an}`. -/
theorem chain_bound (θ : ℝ) {a C : ℝ} (ha : 0 ≤ a) (hC : 1 ≤ C)
    (hCa : ∀ s : ℕ, 1 ≤ s → (smallDivisor θ s)⁻¹ ≤ C * Real.exp (a * s))
    {n r : ℕ} (k : Fin r → ℕ) (hk : StrictMono k) (hkn : ∀ j, 1 ≤ k j ∧ k j ≤ n) :
    ∏ j, max 1 (smallDivisor θ (k j))⁻¹ ≤ (C * n) ^ r * Real.exp (a * n) := by
  have hmem : ∀ s ∈ List.ofFn k, 1 ≤ s ∧ s ≤ n := fun s hs => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hs
    exact hkn j
  have h := prod_le_of_packing θ ha hC hCa (fun s => max 1 (smallDivisor θ s)⁻¹)
    (fun _ => zero_le_one.trans (le_max_left _ _)) (fun _ => le_rfl) (List.ofFn k) hmem
    (fun q _ => chain_packing q _ (List.pairwise_ofFn.2 fun _ _ hij => hk hij) hmem)
  rwa [List.length_ofFn, List.map_ofFn, List.prod_ofFn] at h

/-! ### The rate `τ` and the constant `C_a` -/

/-- The exponential rate `τ = limsup_{n → ∞} log⁺(𝔡_n⁻¹)/n ∈ [0, ∞]` of `dyn:esm:eq:rate`.
For irrational `θ` every `𝔡_n`, `n ≥ 1`, is positive (`smallDivisor_pos`), so `rate θ` is
exactly the source's `τ`. For rational `θ = p/q` the source's `τ` is `∞`, but here
`𝔡_{kq} = 0` and the convention `0⁻¹ = 0` (with `log⁺ 0 = 0`) make `rate θ` finite (in fact
`0`, which is not proved here), not `∞`; `tree_product_bound_of_rate_lt` then holds for
every real `a > rate θ`, with zero factors wherever `q ∣ s_v`. -/
def rate (θ : ℝ) : EReal :=
  Filter.limsup (fun n : ℕ => ((Real.posLog (smallDivisor θ n)⁻¹ / n : ℝ) : EReal))
    Filter.atTop

/-- `τ ≥ 0`, since every term `log⁺(𝔡_n⁻¹)/n` is nonnegative. -/
theorem rate_nonneg (θ : ℝ) : 0 ≤ rate θ :=
  Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall fun n => by
    exact_mod_cast div_nonneg Real.posLog_nonneg (Nat.cast_nonneg n))

/-- A real `a > τ` is positive. -/
theorem pos_of_rate_lt {θ a : ℝ} (h : rate θ < a) : 0 < a :=
  EReal.coe_pos.1 ((rate_nonneg θ).trans_lt h)

/-- The normalized divisors `e^{-as} 𝔡_s⁻¹`, `s ≥ 1`, indexed by `s + 1`. -/
def normalized (θ a : ℝ) (s : ℕ) : ℝ :=
  Real.exp (-(a * ((s + 1 : ℕ) : ℝ))) * (smallDivisor θ (s + 1))⁻¹

/-- The constant `C_a = max(1, sup_{s ≥ 1} e^{-as} 𝔡_s⁻¹)` of `dyn:esm:eq:Ca`. -/
def constC (θ a : ℝ) : ℝ :=
  max 1 (⨆ s : ℕ, normalized θ a s)

/-- `C_a ≥ 1`. -/
theorem one_le_constC (θ a : ℝ) : 1 ≤ constC θ a := le_max_left _ _

/-- For `a > τ` the supremum defining `C_a` is finite. -/
theorem bddAbove_normalized {θ a : ℝ} (h : rate θ < a) :
    BddAbove (Set.range (normalized θ a)) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_lt_of_limsup_lt h)
  have hg0 : ∀ s, 0 ≤ normalized θ a s := fun s =>
    mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 (smallDivisor_nonneg _ _))
  have hsum : 0 ≤ ∑ s ∈ Finset.range N, normalized θ a s :=
    Finset.sum_nonneg fun t _ => hg0 t
  refine ⟨1 + ∑ s ∈ Finset.range N, normalized θ a s, ?_⟩
  rintro _ ⟨s, rfl⟩
  by_cases hs : s < N
  · have := Finset.single_le_sum (fun t _ => hg0 t) (Finset.mem_range.2 hs)
    linarith
  · have hlt : Real.posLog (smallDivisor θ (s + 1))⁻¹ / ((s + 1 : ℕ) : ℝ) < a := by
      exact_mod_cast hN (s + 1) (by omega)
    have hpos : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := by positivity
    have hlog : Real.posLog (smallDivisor θ (s + 1))⁻¹ < a * ((s + 1 : ℕ) : ℝ) :=
      (div_lt_iff₀ hpos).1 hlt
    have hx : 0 ≤ (smallDivisor θ (s + 1))⁻¹ := inv_nonneg.2 (smallDivisor_nonneg _ _)
    have hle : (smallDivisor θ (s + 1))⁻¹ ≤ Real.exp (a * ((s + 1 : ℕ) : ℝ)) := by
      calc (smallDivisor θ (s + 1))⁻¹ ≤ max 1 (smallDivisor θ (s + 1))⁻¹ := le_max_right _ _
        _ = Real.exp (Real.posLog (smallDivisor θ (s + 1))⁻¹) := by
            rw [Real.posLog_eq_log_max_one hx,
              Real.exp_log (lt_of_lt_of_le one_pos (le_max_left _ _))]
        _ ≤ Real.exp (a * ((s + 1 : ℕ) : ℝ)) := Real.exp_le_exp.2 hlog.le
    have : normalized θ a s ≤ 1 := by
      calc normalized θ a s
          ≤ Real.exp (-(a * ((s + 1 : ℕ) : ℝ))) * Real.exp (a * ((s + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    linarith

/-- `dyn:esm:eq:Ca`: for `a > τ`, `𝔡_s⁻¹ ≤ C_a e^{as}` for every `s ≥ 1`. -/
theorem inv_smallDivisor_le_constC {θ a : ℝ} (h : rate θ < a) {s : ℕ} (hs : 1 ≤ s) :
    (smallDivisor θ s)⁻¹ ≤ constC θ a * Real.exp (a * s) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have h2 : normalized θ a t ≤ constC θ a :=
    (le_ciSup (bddAbove_normalized h) t).trans (le_max_right _ _)
  have hE : 0 < Real.exp (a * ((t + 1 : ℕ) : ℝ)) := Real.exp_pos _
  calc (smallDivisor θ (t + 1))⁻¹ = normalized θ a t * Real.exp (a * ((t + 1 : ℕ) : ℝ)) := by
        rw [normalized, mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add, neg_add_cancel,
          Real.exp_zero, mul_one]
    _ ≤ constC θ a * Real.exp (a * ((t + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right h2 hE.le

/-- `dyn:esm:thm:treebound` (tree product bound), in the form of the source: if `a > τ`, then
for every finite rooted forest with positive integer weights, `m` vertices and total weight
`n`, `∏_v 𝔡_{s_v}⁻¹ ≤ (C_a n)^m e^{an}`. -/
theorem tree_product_bound_of_rate_lt {θ a : ℝ} (h : rate θ < a) (F : Forest)
    (hF : F.PosWeights) :
    (F.sums.map fun s => (smallDivisor θ s)⁻¹).prod ≤
      (constC θ a * F.total) ^ F.card * Real.exp (a * F.total) :=
  tree_product_bound θ (pos_of_rate_lt h).le (one_le_constC θ a)
    (fun _ hs => inv_smallDivisor_le_constC h hs) F hF

/-- `dyn:esm:cor:chain` (i), in the form of the source: if `a > τ`, every strictly increasing
chain `1 ≤ k_1 < ⋯ < k_r ≤ n` satisfies `∏_j max(1, 𝔡_{k_j}⁻¹) ≤ (C_a n)^r e^{an}`. -/
theorem chain_bound_of_rate_lt {θ a : ℝ} (h : rate θ < a) {n r : ℕ} (k : Fin r → ℕ)
    (hk : StrictMono k) (hkn : ∀ j, 1 ≤ k j ∧ k j ≤ n) :
    ∏ j, max 1 (smallDivisor θ (k j))⁻¹ ≤ (constC θ a * n) ^ r * Real.exp (a * n) :=
  chain_bound θ (pos_of_rate_lt h).le (one_le_constC θ a)
    (fun _ hs => inv_smallDivisor_le_constC h hs) k hk hkn

end

end Surreal.SmallDivisorTree
