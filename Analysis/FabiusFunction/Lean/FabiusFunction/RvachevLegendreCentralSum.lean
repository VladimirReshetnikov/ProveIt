import FabiusFunction.FabiusLegendreTranslateBlocks
import FabiusFunction.RvachevLagrangeNodesOnly

/-!
# Central cancellation in the Rvachev--Legendre synthesis

The even Legendre synthesis at mesh `4 ^ n` has an especially compact value
at the origin.  The deconvolved Legendre polynomial is even, the support of
`rvachevUp` removes every index with absolute value at least `4 ^ n`, and the
remaining nonzero indices pair under `k ↦ -k`.  Multiplying the synthesis
identity by its mesh therefore gives the finite central-binomial cancellation

`Q_(2n)(0) + 2 * ∑_(0 < k < 4^n) Q_(2n)(k / 4^n) * up(k / 4^n)
  = (-1)^n * (2n).choose n`.

Everything in this module is finite algebra plus the already-proved compact
support and Legendre synthesis theorem.  In particular, the result makes no
claim about the Jacobi closed form for the decoder, reverse spectral closure,
or the larger Lagrange right-inverse package.
-/

set_option autoImplicit false

open Polynomial Set Finset
open scoped BigOperators

namespace Fabius

noncomputable section

/-- The central value of the even Rodrigues-normalized Legendre polynomial.
This is the exact normalization used when the mesh `4 ^ n` is cleared from
the central Rvachev synthesis identity. -/
theorem eval_legendrePolynomial_even_zero (n : ℕ) :
    (legendrePolynomial (2 * n)).eval 0 =
      (-1 : ℝ) ^ n * ((4 : ℝ) ^ n)⁻¹ * ((2 * n).choose n : ℝ) := by
  rw [eval_legendrePolynomial_even]
  have hsum :
      ∑ k ∈ range (n + 1),
          ((-1 : ℝ) ^ (n + k)) *
            (2 * n).choose (n + k) *
            (2 * n + 2 * k).choose (2 * n) * (0 : ℝ) ^ (2 * k) =
        (-1 : ℝ) ^ n * ((2 * n).choose n : ℝ) := by
    rw [sum_eq_single 0]
    · norm_num
    · intro k _hk hk0
      simp
      right
      exact hk0
    · simp
  rw [hsum, inv_pow]
  ring

/-- Rvachev deconvolution preserves the even parity of `P_(2n)`, stated in
the pointwise form used to pair the positive and negative synthesis nodes.
The proof uses the finite even-derivative formula for deconvolution; no
analytic power-series interpretation is needed. -/
theorem eval_rvachevLegendreDeconvolutionPolynomial_even
    (n : ℕ) (x : ℝ) :
    (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval (-x) =
      (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval x := by
  rw [rvachevLegendreDeconvolutionPolynomial,
    eval_rvachevDeconvolvedPolynomial_eq_sum_even_iterateDerivative,
    eval_rvachevDeconvolvedPolynomial_eq_sum_even_iterateDerivative]
  apply Finset.sum_congr rfl
  intro r _hr
  apply congrArg (fun z : ℝ ↦
    (rvachevReciprocalMomentRat (2 * r) : ℝ) *
      (z / ((2 * r).factorial : ℝ)))
  have hparity :
      (legendrePolynomial (2 * n)).comp (-X) =
        legendrePolynomial (2 * n) := by
    simpa [pow_mul] using legendrePolynomial_comp_neg_X (2 * n)
  have hderiv := iterate_derivative_comp_affine
    (legendrePolynomial (2 * n)) (-1) 0 (2 * r)
  have haffine :
      C (-1 : ℝ) * X + C 0 = (-X : ℝ[X]) := by
    simp
  rw [haffine, hparity] at hderiv
  simp only [pow_mul, neg_one_sq, one_pow, one_smul] at hderiv
  have heval := congrArg
    (fun P : ℝ[X] ↦ P.eval x) hderiv
  simp only [eval_comp, eval_neg, eval_X] at heval
  exact heval.symm

private theorem sum_Ioo_even_int
    (f : ℤ → ℝ) {M : ℤ} (hM : 0 < M)
    (heven : ∀ k, f (-k) = f k) :
    ∑ k ∈ Finset.Ioo (-M) M, f k =
      f 0 + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) M, f k := by
  have hsplit :
      Finset.Ioo (-M) M =
        Finset.Ioo (-M) 0 ∪ Finset.Ico 0 M := by
    ext k
    simp only [Finset.mem_Ioo, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisjoint :
      Disjoint (Finset.Ioo (-M) 0) (Finset.Ico 0 M) := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkneg hknonneg
    simp only [Finset.mem_Ioo] at hkneg
    simp only [Finset.mem_Ico] at hknonneg
    omega
  have hneg :
      ∑ k ∈ Finset.Ioo (-M) 0, f k =
        ∑ k ∈ Finset.Ioo (0 : ℤ) M, f k := by
    refine Finset.sum_nbij (fun k : ℤ ↦ -k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Ioo] at hk ⊢
      exact ⟨neg_pos.mpr hk.2, by simpa using neg_lt_neg hk.1⟩
    · intro a ha b hb hab
      exact neg_injective hab
    · intro b hb
      have hbIoo : 0 < b ∧ b < M := Finset.mem_Ioo.mp hb
      refine ⟨-b, ?_, ?_⟩
      · show -b ∈ Finset.Ioo (-M) 0
        exact Finset.mem_Ioo.mpr
          ⟨by simpa using neg_lt_neg hbIoo.2, neg_lt_zero.mpr hbIoo.1⟩
      · simp
    · intro k _hk
      exact (heven k).symm
  have hnonneg :
      ∑ k ∈ Finset.Ico (0 : ℤ) M, f k =
        f 0 + ∑ k ∈ Finset.Ioo (0 : ℤ) M, f k := by
    rw [← Finset.Ioo_insert_left hM, Finset.sum_insert]
    simp
  rw [hsplit, Finset.sum_union hdisjoint, hneg, hnonneg]
  ring

/-- **Central-binomial dyadic cancellation.**  At the exact even-mode mesh
`M = 4 ^ n`, evaluation of the finite Rvachev--Legendre synthesis at zero,
support truncation, and parity pairing give the manuscript's literal finite
sum over `1 ≤ k ≤ M - 1`.  The statement includes `n = 0`, when the
positive-index sum is empty. -/
theorem rvachevLegendreCentralSum
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval 0 +
        2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (4 ^ n : ℤ),
          (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval
              ((k : ℝ) / (4 : ℝ) ^ n) *
            rvachevUp F ((k : ℝ) / (4 : ℝ) ^ n) =
      (-1 : ℝ) ^ n * ((2 * n).choose n : ℝ) := by
  let f : ℤ → ℝ := fun k ↦
    (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval
        ((k : ℝ) / (4 : ℝ) ^ n) *
      rvachevUp F ((k : ℝ) / (4 : ℝ) ^ n)
  have hMZ : (0 : ℤ) < (4 ^ n : ℤ) := by positivity
  have hMR : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hMR0 : (4 : ℝ) ^ n ≠ 0 := hMR.ne'
  have hsynth :
      (legendrePolynomial (2 * n)).eval 0 =
        ((4 : ℝ) ^ n)⁻¹ *
          ∑ k ∈ Finset.Ioo (-(2 * (4 ^ n : ℤ)))
              (2 * (4 ^ n : ℤ)), f k := by
    rw [eval_legendrePolynomial_even_eq_sum_rvachevUp
      F hF n (x := 0) (by constructor <;> norm_num)]
    apply congrArg (fun z : ℝ ↦ ((4 : ℝ) ^ n)⁻¹ * z)
    apply Finset.sum_congr rfl
    intro k _hk
    dsimp only [f]
    rw [zero_sub, rvachevUp_even F]
  have hsubset :
      Finset.Ioo (-(4 ^ n : ℤ)) (4 ^ n : ℤ) ⊆
        Finset.Ioo (-(2 * (4 ^ n : ℤ)))
          (2 * (4 ^ n : ℤ)) := by
    intro k hk
    simp only [Finset.mem_Ioo] at hk ⊢
    constructor <;> omega
  have htruncate :
      ∑ k ∈ Finset.Ioo (-(2 * (4 ^ n : ℤ)))
          (2 * (4 ^ n : ℤ)), f k =
        ∑ k ∈ Finset.Ioo (-(4 ^ n : ℤ))
          (4 ^ n : ℤ), f k := by
    symm
    refine Finset.sum_subset hsubset ?_
    intro k _hkbig hksmall
    have hkout :
        k ≤ -(4 ^ n : ℤ) ∨ (4 ^ n : ℤ) ≤ k := by
      simp only [Finset.mem_Ioo, not_and_or, not_lt] at hksmall
      exact hksmall
    dsimp only [f]
    rw [show rvachevUp F ((k : ℝ) / (4 : ℝ) ^ n) = 0 by
      rcases hkout with hk | hk
      · apply rvachevUp_eq_zero_of_le_neg_one F hF
        rw [div_le_iff₀ hMR]
        norm_num
        exact_mod_cast hk
      · apply rvachevUp_eq_zero_of_one_le F hF
        rw [le_div_iff₀ hMR]
        norm_num
        exact_mod_cast hk,
      mul_zero]
  have hfeven : ∀ k, f (-k) = f k := by
    intro k
    dsimp only [f]
    rw [Int.cast_neg, neg_div,
      eval_rvachevLegendreDeconvolutionPolynomial_even,
      rvachevUp_even F]
  have hpair :
      ∑ k ∈ Finset.Ioo (-(4 ^ n : ℤ)) (4 ^ n : ℤ), f k =
        f 0 + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (4 ^ n : ℤ), f k :=
    sum_Ioo_even_int f hMZ hfeven
  rw [htruncate, hpair] at hsynth
  have hscaled :
      f 0 + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (4 ^ n : ℤ), f k =
        (4 : ℝ) ^ n * (legendrePolynomial (2 * n)).eval 0 := by
    calc
      f 0 + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (4 ^ n : ℤ), f k =
          (4 : ℝ) ^ n * (((4 : ℝ) ^ n)⁻¹ *
            (f 0 + 2 * ∑ k ∈ Finset.Ioo (0 : ℤ)
              (4 ^ n : ℤ), f k)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hMR0, one_mul]
      _ = (4 : ℝ) ^ n * (legendrePolynomial (2 * n)).eval 0 := by
        rw [← hsynth]
  calc
    (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval 0 +
          2 * ∑ k ∈ Finset.Ioo (0 : ℤ) (4 ^ n : ℤ),
            (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval
                ((k : ℝ) / (4 : ℝ) ^ n) *
              rvachevUp F ((k : ℝ) / (4 : ℝ) ^ n) =
        (4 : ℝ) ^ n * (legendrePolynomial (2 * n)).eval 0 := by
      simpa [f, rvachevUp_zero F hF] using hscaled
    _ = (-1 : ℝ) ^ n * ((2 * n).choose n : ℝ) := by
      rw [eval_legendrePolynomial_even_zero]
      field_simp

end

end Fabius
