import FabiusFunction.MonomialCombExactness

/-!
# Polynomial shifted dyadic exactness

The comb volume's *shifted dyadic exactness* theorem in its full
polynomial form: for every level `m`, every real shift `θ`, and every
real polynomial `P` of degree at most `m`,

`∑_{k∈ℤ} P(θ+k)·up(2^{-m}(θ+k)) = ∫ P(x)·up(2^{-m}x) dx`,

by linearity from the monomial case.  The comb samples have finite
support (the up-factor vanishes outside `(-2^m, 2^m)`), so every
interchange is a finite one.

Rescaling the polynomial and the whole-line integral gives the normalized
physical-coordinate rule `integral_polynomial_mul_rvachevUp_eq_dyadic_tsum`,
whose nodes and weights are samples of the Rvachev density itself.
-/

set_option autoImplicit false

open MeasureTheory Real Set

namespace Fabius

/-- The comb samples of any weight have finite support. -/
theorem finite_support_comb (F : BoundedFabius) (hF : IsFabius F)
    (m : ℕ) (θ : ℝ) (g : ℝ → ℝ) :
    (Function.support fun k : ℤ =>
      g (θ + k) * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k))).Finite := by
  refine Set.Finite.subset
    (Set.finite_Icc ⌈-(2 : ℝ) ^ m - θ⌉ ⌊(2 : ℝ) ^ m - θ⌋) ?_
  intro k hk
  have hne : rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k)) ≠ 0 := by
    intro h0
    exact (Function.mem_support.mp hk) (by rw [h0, mul_zero])
  have hmem : ((2 : ℝ) ^ m)⁻¹ * (θ + k) ∈ Ioo (-1 : ℝ) 1 := by
    by_contra hnot
    exact hne (rvachevUp_eq_zero_of_not_mem_Ioo F hF hnot)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h1 : -(2 : ℝ) ^ m < θ + k := by
    have hlt : -1 * (2 : ℝ) ^ m < (((2 : ℝ) ^ m)⁻¹ * (θ + k)) *
        (2 : ℝ) ^ m := by
      nlinarith [hmem.1]
    calc -(2 : ℝ) ^ m = -1 * (2 : ℝ) ^ m := by ring
      _ < (((2 : ℝ) ^ m)⁻¹ * (θ + k)) * (2 : ℝ) ^ m := hlt
      _ = θ + k := by field_simp
  have h2 : θ + (k : ℝ) < (2 : ℝ) ^ m := by
    have hlt : (((2 : ℝ) ^ m)⁻¹ * (θ + k)) * (2 : ℝ) ^ m <
        1 * (2 : ℝ) ^ m := by
      nlinarith [hmem.2]
    calc θ + (k : ℝ) = (((2 : ℝ) ^ m)⁻¹ * (θ + k)) * (2 : ℝ) ^ m := by
          field_simp
      _ < 1 * (2 : ℝ) ^ m := hlt
      _ = (2 : ℝ) ^ m := one_mul _
  constructor
  · rw [Int.ceil_le]
    linarith
  · rw [Int.le_floor]
    linarith

/-- **Shifted dyadic exactness, polynomial form**: for every level
`m`, every real shift `θ`, and every real polynomial `P` with
`deg P ≤ m`,
`∑_{k∈ℤ} P(θ+k)·up(2^{-m}(θ+k)) = ∫ P(x)·up(2^{-m}x) dx`. -/
theorem tsum_shifted_polynomial_eq_integral (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) {P : Polynomial ℝ}
    (hdeg : P.natDegree ≤ m) (θ : ℝ) :
    ∑' k : ℤ, P.eval (θ + k) *
        rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k)) =
      ∫ x : ℝ, P.eval x * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) := by
  have hup_cont : Continuous
      (fun x : ℝ => rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x)) :=
    (rvachev_contDiff F hF).continuous.comp (by fun_prop)
  have hup_supp : HasCompactSupport
      (fun x : ℝ => rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x)) := by
    simpa only [smul_eq_mul] using
      (rvachevUp_hasCompactSupport F hF).comp_smul
        (by positivity : ((2 : ℝ) ^ m)⁻¹ ≠ 0)
  have hint : ∀ i : ℕ, Integrable
      (fun x : ℝ => x ^ i * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x)) :=
    fun i => ((continuous_pow i).mul
      hup_cont).integrable_of_hasCompactSupport (hup_supp.mul_left)
  have hsummable : ∀ i : ℕ, Summable (fun k : ℤ =>
      (θ + k) ^ i * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k))) :=
    fun i => summable_of_hasFiniteSupport
      (finite_support_comb F hF m θ (· ^ i))
  calc ∑' k : ℤ, P.eval (θ + k) *
        rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k))
      = ∑' k : ℤ, ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * ((θ + k) ^ i *
            rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k))) := by
        refine tsum_congr fun k => ?_
        rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * ∑' k : ℤ, (θ + k) ^ i *
            rvachevUp F (((2 : ℝ) ^ m)⁻¹ * (θ + k)) := by
        rw [Summable.tsum_finsetSum fun i _ =>
          ((hsummable i).mul_left (P.coeff i))]
        exact Finset.sum_congr rfl fun i _ => tsum_mul_left
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * ∫ x : ℝ, x ^ i *
            rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ m :=
          le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hdeg
        rw [tsum_shifted_monomial_eq_integral_real F hF m hi' θ]
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          ∫ x : ℝ, P.coeff i * (x ^ i *
            rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x)) :=
        Finset.sum_congr rfl fun i _ =>
          (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ x : ℝ, ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * (x ^ i * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x)) :=
        (integral_finsetSum _ fun i _ => (hint i).const_mul _).symm
    _ = ∫ x : ℝ, P.eval x * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **Shifted dyadic self-sampling quadrature.**  At dyadic mesh
`2⁻ᴺ`, samples of the Rvachev density itself integrate every real
polynomial of degree at most `N`, for an arbitrary real phase `θ`:

`integral P(x) * up(x) dx =
  2⁻ᴺ * ∑ k : ℤ, P(2⁻ᴺ * (θ + k)) * up(2⁻ᴺ * (θ + k))`.

The `tsum` is actually finite by compact support.  This is the normalized,
physical-coordinate form of `tsum_shifted_polynomial_eq_integral`: rescale
the polynomial before applying comb exactness, then change variables in the
whole-line integral. -/
theorem integral_polynomial_mul_rvachevUp_eq_dyadic_tsum
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ)
    {P : Polynomial ℝ} (hdeg : P.natDegree ≤ N) (θ : ℝ) :
    (∫ x : ℝ, P.eval x * rvachevUp F x) =
      ((2 : ℝ) ^ N)⁻¹ *
        ∑' k : ℤ,
          P.eval (((2 : ℝ) ^ N)⁻¹ * (θ + k)) *
            rvachevUp F (((2 : ℝ) ^ N)⁻¹ * (θ + k)) := by
  let Q : Polynomial ℝ :=
    P.comp
      (Polynomial.C (((2 : ℝ) ^ N)⁻¹) * Polynomial.X + Polynomial.C 0)
  have hQdeg : Q.natDegree ≤ N := by
    calc
      Q.natDegree ≤ P.natDegree *
          (Polynomial.C (((2 : ℝ) ^ N)⁻¹) * Polynomial.X +
            Polynomial.C 0).natDegree := by
        exact Polynomial.natDegree_comp_le
      _ ≤ P.natDegree * 1 := by
        exact Nat.mul_le_mul_left P.natDegree Polynomial.natDegree_linear_le
      _ = P.natDegree := by omega
      _ ≤ N := hdeg
  have hcomb := tsum_shifted_polynomial_eq_integral F hF N hQdeg θ
  have hpow : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  have hscale := MeasureTheory.Measure.integral_comp_inv_mul_left
    (fun x : ℝ ↦ P.eval x * rvachevUp F x) ((2 : ℝ) ^ N)
  have hintegral :
      (∫ z : ℝ,
          Q.eval z * rvachevUp F (((2 : ℝ) ^ N)⁻¹ * z)) =
        (2 : ℝ) ^ N * ∫ x : ℝ, P.eval x * rvachevUp F x := by
    calc
      (∫ z : ℝ,
          Q.eval z * rvachevUp F (((2 : ℝ) ^ N)⁻¹ * z)) =
          ∫ z : ℝ,
            P.eval (((2 : ℝ) ^ N)⁻¹ * z) *
              rvachevUp F (((2 : ℝ) ^ N)⁻¹ * z) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
        simp only [Q, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          add_zero]
      _ = (2 : ℝ) ^ N * ∫ x : ℝ, P.eval x * rvachevUp F x := by
        simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ N),
          smul_eq_mul] using hscale
  calc
    (∫ x : ℝ, P.eval x * rvachevUp F x) =
        ((2 : ℝ) ^ N)⁻¹ *
          ((2 : ℝ) ^ N * ∫ x : ℝ, P.eval x * rvachevUp F x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
    _ = ((2 : ℝ) ^ N)⁻¹ *
          ∫ z : ℝ,
            Q.eval z * rvachevUp F (((2 : ℝ) ^ N)⁻¹ * z) := by
      rw [hintegral]
    _ = ((2 : ℝ) ^ N)⁻¹ *
          ∑' k : ℤ,
            Q.eval (θ + k) *
              rvachevUp F (((2 : ℝ) ^ N)⁻¹ * (θ + k)) := by
      rw [hcomb]
    _ = ((2 : ℝ) ^ N)⁻¹ *
          ∑' k : ℤ,
            P.eval (((2 : ℝ) ^ N)⁻¹ * (θ + k)) *
              rvachevUp F (((2 : ℝ) ^ N)⁻¹ * (θ + k)) := by
      apply congrArg (fun s : ℝ ↦ ((2 : ℝ) ^ N)⁻¹ * s)
      exact tsum_congr fun k ↦ by
        simp only [Q, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          add_zero]

end Fabius
