import FabiusFunction.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Symmetric grid sums and exact trapezoidal quadrature

The dyadic-comb drafts study the Riemann sums
`L_{N,p} = M⁻¹ ∑_{k<M} (k/M)^p F(k/M)` at dyadic sizes `M = 2^N` and
prove exactness phenomena for the trapezoidal normalization.  At order
`p = 0` the deepest such statement is completely elementary — it needs
only the reflection symmetry `F(1-x) = 1 - F(x)`, holds for **every**
grid size `M` (not only dyadic ones), and this module proves it that
way:

* `sum_symmetric_grid` — for any function with the reflection symmetry
  `g(1-x) = 1 - g(x)`, the interior grid samples pair up:
  `∑_{k=1}^{M-1} g(k/M) = (M-1)/2`.
* `trapezoid_symmetric` — hence the trapezoidal sum is exactly `½`,
  with the endpoint weights supplied by the symmetry itself
  (`g(0) + g(1) = 1`).
* `integral_fabiusReal_unit` — `∫₀¹ F = ½`, again by reflection.
* `fabius_trapezoid_exact` — **the trapezoidal rule is exact for the
  Fabius function on every uniform partition of `[0,1]`**: the
  trapezoidal sum equals `∫₀¹ F` for every `M ≥ 1`.  The drafts state
  the dyadic case; the symmetry argument gives all `M` at once.
-/

set_option autoImplicit false

open Finset

namespace Fabius

section Symmetric

variable {g : ℝ → ℝ}

/-- **Interior samples of a reflection-symmetric function pair to
one**: if `g(1-x) = 1 - g(x)`, then `∑_{k=1}^{M-1} g(k/M) = (M-1)/2`
for every grid size `M ≥ 1`. -/
theorem sum_symmetric_grid (hsym : ∀ x, g (1 - x) = 1 - g x)
    {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Ico 1 M, g ((k : ℝ) / M) = ((M : ℝ) - 1) / 2 := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ∑ k ∈ Finset.Ico 1 M, g ((k : ℝ) / M) =
      ∑ j ∈ Finset.range (M - 1), g (((1 + j : ℕ) : ℝ) / M) := by
    rw [Finset.sum_Ico_eq_sum_range]
  have h2 : ∑ j ∈ Finset.range (M - 1), g (((1 + j : ℕ) : ℝ) / M) =
      ∑ j ∈ Finset.range (M - 1),
        g (((1 + (M - 1 - 1 - j) : ℕ) : ℝ) / M) :=
    (Finset.sum_range_reflect
      (fun j => g (((1 + j : ℕ) : ℝ) / M)) (M - 1)).symm
  have hpair : ∀ j ∈ Finset.range (M - 1),
      g (((1 + (M - 1 - 1 - j) : ℕ) : ℝ) / M) +
        g (((1 + j : ℕ) : ℝ) / M) = 1 := by
    intro j hj
    have hjlt : j < M - 1 := Finset.mem_range.mp hj
    have hnat : (1 + (M - 1 - 1 - j)) + (1 + j) = M := by omega
    have hcast : ((1 + (M - 1 - 1 - j) : ℕ) : ℝ) =
        (M : ℝ) - ((1 + j : ℕ) : ℝ) := by
      have hc := congrArg (Nat.cast : ℕ → ℝ) hnat
      push_cast at hc ⊢
      linarith
    have hdiv : (((1 + (M - 1 - 1 - j) : ℕ) : ℝ) / M) =
        1 - ((1 + j : ℕ) : ℝ) / M := by
      rw [hcast]
      field_simp
    rw [hdiv, hsym]
    ring
  have hsum2 : (2 : ℝ) * ∑ k ∈ Finset.Ico 1 M, g ((k : ℝ) / M) =
      (M : ℝ) - 1 := by
    rw [two_mul, h1]
    nth_rewrite 1 [h2]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hpair,
      Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range,
      Nat.cast_sub hM, Nat.cast_one]
  linarith

/-- **The trapezoidal sum of a reflection-symmetric function is
exactly `½`** on every uniform grid: the endpoint weights come from
the symmetry itself, `g(0) + g(1) = 1`. -/
theorem trapezoid_symmetric (hsym : ∀ x, g (1 - x) = 1 - g x)
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ k ∈ Finset.Ico 1 M, g ((k : ℝ) / M)) / M +
      (g 0 + g 1) / (2 * M) = 1 / 2 := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h01 : g 0 + g 1 = 1 := by
    have h := hsym 0
    rw [sub_zero] at h
    linarith
  rw [sum_symmetric_grid hsym hM, h01]
  field_simp
  ring

end Symmetric

section FabiusInstance

/-- The interior dyadic (indeed arbitrary-grid) samples of the Fabius
function pair to one: `∑_{k=1}^{M-1} F(k/M) = (M-1)/2`. -/
theorem fabius_sum_symmetric_grid (F : BoundedFabius) (hF : IsFabius F)
    {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Ico 1 M, fabiusReal F ((k : ℝ) / M) =
      ((M : ℝ) - 1) / 2 :=
  sum_symmetric_grid hF.symmetry_all hM

/-- The unit integral of the Fabius function is `½`, by reflection. -/
theorem integral_fabiusReal_unit (F : BoundedFabius) (hF : IsFabius F) :
    ∫ x in (0 : ℝ)..1, fabiusReal F x = 1 / 2 := by
  have hInt : IntervalIntegrable (fabiusReal F) MeasureTheory.volume
      0 1 := (hF.contDiff.continuous).intervalIntegrable 0 1
  have hrefl : ∫ x in (0 : ℝ)..1, fabiusReal F (1 - x) =
      ∫ x in (0 : ℝ)..1, fabiusReal F x := by
    rw [intervalIntegral.integral_comp_sub_left (fabiusReal F) 1]
    norm_num
  have hcongr : ∫ x in (0 : ℝ)..1, fabiusReal F (1 - x) =
      ∫ x in (0 : ℝ)..1, (1 - fabiusReal F x) :=
    intervalIntegral.integral_congr fun x _ => hF.symmetry_all x
  rw [hcongr, intervalIntegral.integral_sub
    intervalIntegrable_const hInt,
    intervalIntegral.integral_const] at hrefl
  simp only [sub_zero, smul_eq_mul, mul_one] at hrefl
  linarith

/-- **The trapezoidal rule is exact for the Fabius function on every
uniform partition of `[0,1]`**: for every `M ≥ 1`,
`M⁻¹ ∑_{k=1}^{M-1} F(k/M) + (F(0)+F(1))/(2M) = ∫₀¹ F`.  The
dyadic-comb drafts state the dyadic sizes `M = 2^N`; the reflection
symmetry gives all grid sizes at once. -/
theorem fabius_trapezoid_exact (F : BoundedFabius) (hF : IsFabius F)
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ k ∈ Finset.Ico 1 M, fabiusReal F ((k : ℝ) / M)) / M +
      (fabiusReal F 0 + fabiusReal F 1) / (2 * M) =
      ∫ x in (0 : ℝ)..1, fabiusReal F x := by
  rw [integral_fabiusReal_unit F hF]
  exact trapezoid_symmetric hF.symmetry_all hM

end FabiusInstance

section OddComb

/-- **Centered odd-power Rvachev comb sums vanish at every real
scale**: `∑_{k∈ℤ} (uk)^{2r+1}·up(uk) = 0` for every `u` and `r`, by
evenness of `up` alone.  This is the odd half of the comb volume's
centered-moment corollary, valid at arbitrary — not only dyadic —
scales and with no level restriction. -/
theorem tsum_odd_pow_mul_rvachevUp (F : BoundedFabius) (u : ℝ)
    (r : ℕ) :
    ∑' k : ℤ, (u * k) ^ (2 * r + 1) * rvachevUp F (u * k) = 0 := by
  have hneg : ∀ k : ℤ,
      (u * ((-k : ℤ) : ℝ)) ^ (2 * r + 1) *
        rvachevUp F (u * ((-k : ℤ) : ℝ)) =
      -((u * k) ^ (2 * r + 1) * rvachevUp F (u * k)) := by
    intro k
    have h1 : (u * ((-k : ℤ) : ℝ)) = -(u * k) := by
      push_cast
      ring
    rw [h1, (rvachevUp_even F) (u * k),
      Odd.neg_pow ⟨r, by ring⟩]
    ring
  have key : ∑' k : ℤ, (u * k) ^ (2 * r + 1) * rvachevUp F (u * k) =
      -∑' k : ℤ, (u * k) ^ (2 * r + 1) * rvachevUp F (u * k) := by
    conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq
      (fun k : ℤ => (u * k) ^ (2 * r + 1) * rvachevUp F (u * k))]
    have hterm : ∀ k : ℤ,
        (fun k : ℤ => (u * k) ^ (2 * r + 1) * rvachevUp F (u * k))
          ((Equiv.neg ℤ) k) =
        -((u * k) ^ (2 * r + 1) * rvachevUp F (u * k)) := by
      intro k
      simp only [Equiv.neg_apply]
      exact hneg k
    rw [tsum_congr hterm, tsum_neg]
  linarith

end OddComb

end Fabius
