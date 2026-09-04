import FabiusFunction.Differential
import FabiusFunction.DyadicClosedForm
import FabiusFunction.GlobalExtension

/-!
# The dyadic derivative filtration

The spectra volume's `p1:thm:dyadic-filtration`, in its two exact parts.  At a
reduced dyadic point `t = a/2^n` (`a` odd), the derivatives of the up-function
satisfy

* `up^{(m)}(t) = 0` for every `m > n`  (`p1:eq:filtration-above`), and
* `up^{(n)}(t) = -ε_{(a-1)/2} · 2^{n(n+1)/2}`  (`p1:eq:filtration-critical`).

Both come from the corpus's closed form for the derivatives as finite
Thue–Morse sums of translates, `iteratedDeriv_rvachevUp_eq_thueMorse_sum`:

`up^{(m)}(x) = 2^{m(m+1)/2} ∑_{j<2^m} ε_j · up(2^m x + 2^m - 1 - 2j)`.

At `x = a/2^n` with `m > n` every translate argument is an odd integer, where
`up` vanishes; at `m = n` every argument is an even integer, and the single
one that vanishes, `j = (a-1)/2 + 2^{n-1}`, carries the sign
`ε_{(a-1)/2 + 2^{n-1}} = -ε_{(a-1)/2}` by the block-complement law.  The
third part of the volume's theorem, the values for `m < n` through the global
Fabius function, is not treated here.

The volume normalizes `S_m = up^{(m)}/π^m`; the statements below are for the
derivatives themselves.
-/

set_option autoImplicit false

namespace Fabius

open Finset

/-- `up` vanishes at every real of absolute value at least `1`. -/
theorem rvachevUp_eq_zero_of_one_le_abs (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : 1 ≤ |x|) : rvachevUp F x = 0 := by
  rcases le_abs.mp hx with h | h
  · exact rvachevUp_eq_zero_of_one_le F hF h
  · exact rvachevUp_eq_zero_of_le_neg_one F hF (by linarith)

/-- **`p1:eq:filtration-above`**: above the dyadic depth, every derivative
vanishes at `a/2^n`, `a` odd. -/
theorem iteratedDeriv_rvachevUp_dyadic_eq_zero (F : BoundedFabius) (hF : IsFabius F)
    {n m a : ℕ} (hnm : n < m) (ha : Odd a) :
    iteratedDeriv m (rvachevUp F) ((a : ℝ) / 2 ^ n) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k + 1 := ⟨m - n - 1, by omega⟩
  obtain ⟨c, rfl⟩ := ha
  rw [iteratedDeriv_rvachevUp_eq_thueMorse_sum F hF]
  rw [sum_eq_zero, mul_zero]
  intro j _
  -- the translate argument is the odd integer `2(2^k(2c+1) + 2^{n+k} - j) - 1`
  have h2n : ((2 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have harg : (2 : ℝ) ^ (n + k + 1) * (((2 * c + 1 : ℕ) : ℝ) / 2 ^ n) +
      2 ^ (n + k + 1) - 1 - 2 * (j : ℝ)
      = (((2 * (2 ^ k * (2 * c + 1) + 2 ^ (n + k) - j) - 1 : ℤ)) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [harg]
  have hodd : (2 * (2 ^ k * (2 * c + 1) + 2 ^ (n + k) - j) - 1 : ℤ) ≠ 0 := by
    generalize (2 ^ k * (2 * c + 1) + 2 ^ (n + k) - j : ℤ) = u
    omega
  have hge : (1 : ℝ) ≤ |(((2 * (2 ^ k * (2 * c + 1) + 2 ^ (n + k) - j) - 1 : ℤ)) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hodd
  rw [rvachevUp_eq_zero_of_one_le_abs F hF hge, mul_zero]

/-- **`p1:eq:filtration-critical`**: at the critical depth the derivative is a
single signed power of two,

`up^{(n)}((2c+1)/2^n) = -ε_c · 2^{n(n+1)/2}` for `c < 2^{n-1}`, `n ≥ 1`. -/
theorem iteratedDeriv_rvachevUp_dyadic_critical (F : BoundedFabius) (hF : IsFabius F)
    {n : ℕ} (hn : 1 ≤ n) {c : ℕ} (hc : c < 2 ^ (n - 1)) :
    iteratedDeriv n (rvachevUp F) (((2 * c + 1 : ℕ) : ℝ) / 2 ^ n)
      = -((thueMorseSign c : ℤ) : ℝ) * 2 ^ ((n + 1).choose 2) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hc
  rw [iteratedDeriv_rvachevUp_eq_thueMorse_sum F hF]
  have h2 : ((2 : ℝ) ^ (p + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  -- the translate argument at `j` is the even integer `2 (c + 2^p - j)`
  have harg : ∀ j : ℕ, (2 : ℝ) ^ (p + 1) * (((2 * c + 1 : ℕ) : ℝ) / 2 ^ (p + 1)) +
      2 ^ (p + 1) - 1 - 2 * (j : ℝ) = (((2 * ((c : ℤ) + 2 ^ p - j) : ℤ)) : ℝ) := by
    intro j
    push_cast
    rw [pow_succ]
    field_simp
    ring
  have hmem : c + 2 ^ p ∈ range (2 ^ (p + 1)) := by
    rw [mem_range, pow_succ]
    omega
  rw [sum_eq_single_of_mem (c + 2 ^ p) hmem]
  · rw [harg]
    have h0 : (((2 * ((c : ℤ) + 2 ^ p - ((c + 2 ^ p : ℕ) : ℤ)) : ℤ)) : ℝ) = 0 := by
      push_cast
      ring
    rw [h0, rvachevUp_zero F hF, mul_one, add_comm c, thueMorseSign_add_pow_two p c hc]
    push_cast
    ring
  · intro j _ hj
    rw [harg]
    have hne : (2 * ((c : ℤ) + 2 ^ p - j) : ℤ) ≠ 0 := by
      intro h
      apply hj
      have : (j : ℤ) = c + 2 ^ p := by
        generalize hu : (c : ℤ) + 2 ^ p = u at h ⊢
        omega
      exact_mod_cast this
    have hge : (1 : ℝ) ≤ |(((2 * ((c : ℤ) + 2 ^ p - j) : ℤ)) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hne
    rw [rvachevUp_eq_zero_of_one_le_abs F hF hge, mul_zero]

/-- **`p1:cor:denominator-detection`**: at a reduced dyadic point `(2c+1)/2^n`
the critical derivative is nonzero and every higher one vanishes, so the
depth `n` is `max {m : up^{(m)}(t) ≠ 0}`. -/
theorem dyadic_depth_eq_max_nonzero_iteratedDeriv (F : BoundedFabius) (hF : IsFabius F)
    {n : ℕ} (hn : 1 ≤ n) {c : ℕ} (hc : c < 2 ^ (n - 1)) :
    iteratedDeriv n (rvachevUp F) (((2 * c + 1 : ℕ) : ℝ) / 2 ^ n) ≠ 0 ∧
      ∀ m, n < m → iteratedDeriv m (rvachevUp F) (((2 * c + 1 : ℕ) : ℝ) / 2 ^ n) = 0 := by
  refine ⟨?_, fun m hm => iteratedDeriv_rvachevUp_dyadic_eq_zero F hF hm ⟨c, rfl⟩⟩
  rw [iteratedDeriv_rvachevUp_dyadic_critical F hF hn hc]
  have hsign : ((thueMorseSign c : ℤ) : ℝ) ≠ 0 := by
    rw [thueMorseSign]
    push_cast
    exact pow_ne_zero _ (by norm_num)
  exact mul_ne_zero (neg_ne_zero.mpr hsign) (pow_ne_zero _ two_ne_zero)

/-! ## Below the depth: every derivative is a rescaled global value

The volume's third filtration case, `p1:eq:filtration-below`, reads
`S_m(a/2^n) = 2^{m(m+1)/2} π^{-m} F((2^n + a)/2^{n-m})` for `0 ≤ m < n`.
Since `(2^n + a)/2^{n-m} = 2^m (1 + a/2^n)`, it is the composite of two facts
already in the corpus, and neither of them needs the argument to be dyadic or
the order to be below the depth:

* on `(-∞, 1)` the up-function is a single translate of the signed extension
  (`extendedFabius_add_one_eq_rvachevUp`), so their derivatives agree there;
* every iterated derivative of the extension is a rescaled global value
  (`iteratedDeriv_extendedFabius`).

The statement below is therefore strictly more general than the volume's: it
holds at every `x < 1` and for every order `m`. -/

/-- **`p1:eq:filtration-below`, generalized.**  For every order `m` and every
`x < 1`, `up^{(m)}(x) = 2^{m(m+1)/2} F(2^m (1 + x))`. -/
theorem iteratedDeriv_rvachevUp_eq_extendedFabius (F : BoundedFabius) (hF : IsFabius F)
    (m : ℕ) {x : ℝ} (hx : x < 1) :
    iteratedDeriv m (rvachevUp F) x
      = 2 ^ ((m + 1).choose 2) * extendedFabius F (2 ^ m * (x + 1)) := by
  have hev : (fun y : ℝ => rvachevUp F y) =ᶠ[nhds x] fun y : ℝ => extendedFabius F (y + 1) := by
    filter_upwards [(isOpen_Iio (a := (1 : ℝ))).mem_nhds hx] with y hy
    exact (extendedFabius_add_one_eq_rvachevUp F hF (le_of_lt hy)).symm
  rw [hev.iteratedDeriv_eq m, iteratedDeriv_comp_add_const,
    iteratedDeriv_extendedFabius F hF m (x + 1)]

/-- The volume's own form, at a dyadic point: for `a ≤ 2^n` and `m < n`,
`up^{(m)}(a/2^n) = 2^{m(m+1)/2} F((2^n + a)/2^{n-m})`. -/
theorem iteratedDeriv_rvachevUp_dyadic_below (F : BoundedFabius) (hF : IsFabius F)
    {n m a : ℕ} (hmn : m < n) (ha : a < 2 ^ n) :
    iteratedDeriv m (rvachevUp F) ((a : ℝ) / 2 ^ n)
      = 2 ^ ((m + 1).choose 2) *
          extendedFabius F (((2 ^ n + a : ℕ) : ℝ) / 2 ^ (n - m)) := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hx : (a : ℝ) / 2 ^ n < 1 := by
    rw [div_lt_one h2n]
    exact_mod_cast ha
  rw [iteratedDeriv_rvachevUp_eq_extendedFabius F hF m hx]
  congr 2
  have hnm : n - m + m = n := by omega
  have h2 : (2 : ℝ) ^ (n - m) ≠ 0 := by positivity
  rw [eq_div_iff h2]
  push_cast
  field_simp
  rw [← pow_add, hnm]
  ring

end Fabius
