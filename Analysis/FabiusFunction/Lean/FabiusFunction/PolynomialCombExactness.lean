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
    push_cast
    linarith
  · rw [Int.le_floor]
    push_cast
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
        rw [tsum_sum fun i _ => ((hsummable i).mul_left (P.coeff i))]
        exact Finset.sum_congr rfl fun i _ => tsum_mul_left
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * ∫ x : ℝ, x ^ i *
            rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ m :=
          le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hdeg
        rw [tsum_shifted_monomial_eq_integral_real F hF m hi' θ]
    _ = ∫ x : ℝ, P.eval x * rvachevUp F (((2 : ℝ) ^ m)⁻¹ * x) := by
        rw [← integral_finsetSum _ fun i _ => (hint i).const_mul _]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
        exact (Finset.sum_congr rfl fun i _ => by ring).symm

end Fabius
