import Mathlib.Analysis.Calculus.Taylor

/-!
# Zero-initial Volterra primitives from Taylor's theorem

Taylor's theorem with integral remainder contains a useful uniqueness principle
that is easy to obscure when used through its polynomial interface: a smooth
function whose first prescribed jet at a base point vanishes is exactly the
Volterra integral of its first nonzero derivative.

This module packages that principle once, over an arbitrary real Banach space.
It is the reusable calculus layer behind the exact primitive ladders for the
Fabius function, but it has no Fabius-specific dependencies.

## Main definitions and results

* `volterraIntegral` is the normalized Volterra integral of order `n + 1`.
* `eq_taylor_sum_add_volterraIntegral_of_iteratedDeriv` splits a smooth
  function into its initial Taylor jet and its Volterra remainder.
* `volterraIntegral_eq_of_iteratedDeriv` identifies it with any smooth function
  having the corresponding zero initial jet and top derivative.
-/

set_option autoImplicit false

open Set
open scoped Interval

namespace Fabius

/-- The normalized Volterra integral of order `n + 1`, based at `a`:
`Vₙ(f; a, x) = ∫ t in a..x, ((x - t)^n / n!) • f t`.

The index is the exponent of the Cauchy kernel, so `volterraIntegral 0` is the
ordinary interval integral. -/
noncomputable def volterraIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (a x : ℝ) : E :=
  ∫ t in a..x, ((x - t) ^ n / n.factorial) • f t

/-- The zeroth Volterra kernel is the ordinary interval integral. -/
@[simp]
theorem volterraIntegral_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a x : ℝ) :
    volterraIntegral 0 f a x = ∫ t in a..x, f t := by
  simp [volterraIntegral]

/-- Taylor's formula in normalized Volterra notation: a smooth function is
the sum of its degree-`n` jet at `a` and the Volterra integral of its
`(n + 1)`st derivative.

Only the top-derivative identity on the unoriented segment from `a` to `x` is
needed.  The statement is valid in any real Banach space and for either
ordering of the endpoints. -/
theorem eq_taylor_sum_add_volterraIntegral_of_iteratedDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} {f g : ℝ → E} {a x : ℝ}
    (hg : ContDiff ℝ (n + 1 : ℕ) g)
    (hderiv : ∀ t ∈ uIcc a x, iteratedDeriv (n + 1) g t = f t) :
    g x =
      (∑ k ∈ Finset.range (n + 1),
        ((x - a) ^ k / (k.factorial : ℝ)) • iteratedDeriv k g a) +
        volterraIntegral n f a x := by
  by_cases hax : a = x
  · subst x
    rw [volterraIntegral, intervalIntegral.integral_same, add_zero,
      Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      simp [hk0]
    · simp
  have hs : UniqueDiffOn ℝ (uIcc a x) := uniqueDiffOn_uIcc hax
  have ht := taylor_integral_remainder (hg.contDiffOn :
    ContDiffOn ℝ (n + 1 : ℕ) g (uIcc a x))
  have hTaylor :
      taylorWithinEval g n (uIcc a x) a x =
        ∑ k ∈ Finset.range (n + 1),
          ((x - a) ^ k / (k.factorial : ℝ)) • iteratedDeriv k g a := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    rw [iteratedDerivWithin_eq_iteratedDeriv hs
      (hg.contDiffAt.of_le (by
        exact_mod_cast hkn.trans (Nat.le_succ n))) left_mem_uIcc]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  have hIntegral :
      (∫ t in a..x,
          ((x - t) ^ n / (n.factorial : ℝ)) •
            iteratedDerivWithin (n + 1) g (uIcc a x) t) =
        volterraIntegral n f a x := by
    apply intervalIntegral.integral_congr
    intro t htmem
    change ((x - t) ^ n / (n.factorial : ℝ)) •
        iteratedDerivWithin (n + 1) g (uIcc a x) t =
      ((x - t) ^ n / (n.factorial : ℝ)) • f t
    rw [iteratedDerivWithin_eq_iteratedDeriv hs hg.contDiffAt htmem,
      hderiv t htmem]
  rw [hTaylor, hIntegral] at ht
  have h := sub_eq_iff_eq_add.mp ht
  simpa only [add_comm] using h

/-- A smooth function with zero derivatives through order `n` at `a` is the
normalized Volterra integral of its `(n + 1)`st derivative.

Only the derivative identity on the unoriented segment from `a` to `x` is
needed.  The theorem is valid in any real Banach space and for either ordering
of the endpoints. -/
theorem volterraIntegral_eq_of_iteratedDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} {f g : ℝ → E} {a x : ℝ}
    (hg : ContDiff ℝ (n + 1 : ℕ) g)
    (hzero : ∀ k ≤ n, iteratedDeriv k g a = 0)
    (hderiv : ∀ t ∈ uIcc a x, iteratedDeriv (n + 1) g t = f t) :
    volterraIntegral n f a x = g x := by
  have h := eq_taylor_sum_add_volterraIntegral_of_iteratedDeriv hg hderiv
  have hTaylor :
      (∑ k ∈ Finset.range (n + 1),
        ((x - a) ^ k / (k.factorial : ℝ)) • iteratedDeriv k g a) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k ≤ n := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    rw [hzero k hkn, smul_zero]
  rw [hTaylor, zero_add] at h
  exact h.symm

end Fabius
