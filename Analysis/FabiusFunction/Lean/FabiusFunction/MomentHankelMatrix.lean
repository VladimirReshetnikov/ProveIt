import FabiusFunction.WeakConvergence
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive definite moment Hankel matrices of the up-measure

The integration volume's *orthogonal-polynomial layer* obligation
begins: construct `a_n = h_n/h_{n-1}` from Hankel positivity.  This
module supplies exactly that first stage, for the up-measure:

* `upMoment F k = ∫ t^k dμ_up` — the continuous moments (integrable
  because the density is bounded with compact support);
* `momentHankel F n` — the `n × n` Hankel moment matrix
  `(m_{i+j})_{i,j}`;
* `dotProduct_momentHankel_mulVec` — the quadratic form is the
  squared-polynomial moment `cᵀ H c = ∫ (∑ c_i t^i)² dμ`;
* `momentHankel_posDef` — **the Hankel matrix is positive definite**:
  a nonzero coefficient vector gives a nonzero polynomial, which has
  finitely many roots, while the up-measure charges `(-1,1)` with
  full mass and annihilates finite sets — so the squared-polynomial
  moment is strictly positive;
* `hankelDet_pos` and `hankelRatio_pos` — every Hankel determinant
  `h_n` is positive, so the Jacobi ratios `a_n = h_{n+1}/h_n` are
  well-defined and positive.

The finite J-fraction convergents and the exact certificates for the
first coefficients are the obligation's remaining stages.
-/

set_option autoImplicit false

open MeasureTheory Set Matrix
open scoped ENNReal

namespace Fabius

/-- Every monomial is integrable against the up-measure: the density
is bounded with compact support. -/
theorem integrable_pow_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k) (rvachevMeasure F) := by
  rw [rvachevMeasure, integrable_withDensity_iff
    ((rvachev_contDiff F hF).continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hshape : (fun x : ℝ =>
      x ^ k * (ENNReal.ofReal (rvachevUp F x)).toReal) =
      fun x => x ^ k * rvachevUp F x :=
    funext fun x => by rw [ENNReal.toReal_ofReal (rvachevUp_nonneg F x)]
  rw [hshape]
  exact ((continuous_pow k).mul
    (rvachev_contDiff F hF).continuous).integrable_of_hasCompactSupport
    ((rvachevUp_hasCompactSupport F hF).mul_left)

/-- The continuous moments `m_k = ∫ t^k dμ_up` of the up-measure. -/
noncomputable def upMoment (F : BoundedFabius) (k : ℕ) : ℝ :=
  ∫ t, t ^ k ∂(rvachevMeasure F)

/-- The `n × n` Hankel moment matrix `(m_{i+j})_{i,j}`. -/
noncomputable def momentHankel (F : BoundedFabius) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => upMoment F ((i : ℕ) + j)

/-- **The Hankel quadratic form is a squared-polynomial moment**:
`cᵀ H c = ∫ (∑ c_i t^i)² dμ_up`. -/
theorem dotProduct_momentHankel_mulVec (F : BoundedFabius)
    (hF : IsFabius F) {n : ℕ} (c : Fin n → ℝ) :
    c ⬝ᵥ ((momentHankel F n) *ᵥ c) =
      ∫ t, (∑ i, c i * t ^ (i : ℕ)) ^ 2 ∂(rvachevMeasure F) := by
  have hexp : ∀ t : ℝ, (∑ i, c i * t ^ (i : ℕ)) ^ 2 =
      ∑ i, ∑ j, c i * c j * t ^ ((i : ℕ) + (j : ℕ)) := by
    intro t
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by
        rw [pow_add]
        ring
  have hint : ∀ i j : Fin n, Integrable
      (fun t : ℝ => c i * c j * t ^ ((i : ℕ) + (j : ℕ)))
      (rvachevMeasure F) := fun i j =>
    (integrable_pow_rvachevMeasure F hF _).const_mul _
  have hRHS : ∫ t, (∑ i, c i * t ^ (i : ℕ)) ^ 2 ∂(rvachevMeasure F) =
      ∑ i, ∑ j, c i * c j * upMoment F ((i : ℕ) + j) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MeasureTheory.integral_const_mul]
    rfl
  rw [hRHS]
  simp only [dotProduct, Matrix.mulVec, momentHankel,
    Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The up-measure annihilates finite sets. -/
theorem rvachevMeasure_finite_eq_zero (F : BoundedFabius) {s : Set ℝ}
    (hs : s.Finite) : rvachevMeasure F s = 0 :=
  withDensity_absolutelyContinuous volume _ (hs.measure_zero volume)

/-- The up-measure gives the open support `(-1,1)` full mass. -/
theorem rvachevMeasure_Ioo_eq_one (F : BoundedFabius)
    (hF : IsFabius F) :
    rvachevMeasure F (Ioo (-1 : ℝ) 1) = 1 := by
  haveI := rvachevMeasure_isProbability F hF
  rw [← prob_compl_eq_zero_iff measurableSet_Ioo]
  rw [rvachevMeasure, withDensity_apply _ measurableSet_Ioo.compl]
  have hzero : EqOn (fun x : ℝ => ENNReal.ofReal (rvachevUp F x))
      (fun _ => (0 : ℝ≥0∞)) (Ioo (-1 : ℝ) 1)ᶜ := by
    intro x hx
    simp only
    rw [rvachevUp_eq_zero_of_not_mem_Ioo F hF hx, ENNReal.ofReal_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioo.compl hzero]
  simp

/-- **The Hankel moment matrix is positive definite.** -/
theorem momentHankel_posDef (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) : (momentHankel F n).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · show (momentHankel F n)ᴴ = momentHankel F n
    ext i j
    simp only [Matrix.conjTranspose_apply, momentHankel,
      Matrix.of_apply, star_trivial]
    rw [Nat.add_comm]
  · intro x hx
    have hstar : star x = x := funext fun i => star_trivial (x i)
    rw [hstar, dotProduct_momentHankel_mulVec F hF x]
    have hnonneg : 0 ≤ᵐ[rvachevMeasure F]
        fun t => (∑ i, x i * t ^ (i : ℕ)) ^ 2 :=
      Filter.Eventually.of_forall fun t => sq_nonneg _
    have hint : Integrable (fun t => (∑ i, x i * t ^ (i : ℕ)) ^ 2)
        (rvachevMeasure F) := by
      have hexp : (fun t : ℝ => (∑ i, x i * t ^ (i : ℕ)) ^ 2) =
          fun t => ∑ i, ∑ j, x i * x j * t ^ ((i : ℕ) + (j : ℕ)) := by
        funext t
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by
            rw [pow_add]
            ring
      rw [hexp]
      exact integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ =>
          (integrable_pow_rvachevMeasure F hF _).const_mul _
    rw [integral_pos_iff_support_of_nonneg_ae hnonneg hint]
    set p : Polynomial ℝ :=
      ∑ i : Fin n, Polynomial.C (x i) * Polynomial.X ^ (i : ℕ) with hp
    have heval : ∀ t : ℝ, p.eval t = ∑ i, x i * t ^ (i : ℕ) := by
      intro t
      rw [hp]
      simp [Polynomial.eval_finsetSum]
    have hcoeff : ∀ i₀ : Fin n, p.coeff (i₀ : ℕ) = x i₀ := by
      intro i₀
      rw [hp, Polynomial.finsetSum_coeff]
      have hterm : ∀ i : Fin n,
          (Polynomial.C (x i) * Polynomial.X ^ (i : ℕ)).coeff
            (i₀ : ℕ) = if i₀ = i then x i else 0 := by
        intro i
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        by_cases h : i₀ = i
        · subst h
          simp
        · rw [if_neg (fun hval => h (Fin.val_injective hval)),
            mul_zero, if_neg h]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq Finset.univ i₀ (fun i => x i),
        if_pos (Finset.mem_univ _)]
    have hpne : p ≠ 0 := by
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
      intro h0
      apply hi₀
      have := hcoeff i₀
      rw [h0, Polynomial.coeff_zero] at this
      exact this.symm
    have hsupp : Ioo (-1 : ℝ) 1 \ {t | p.IsRoot t} ⊆
        Function.support fun t => (∑ i, x i * t ^ (i : ℕ)) ^ 2 := by
      intro t ht
      simp only [Function.mem_support]
      intro h0
      refine ht.2 ?_
      show p.IsRoot t
      rw [Polynomial.IsRoot, heval t]
      exact (pow_eq_zero_iff two_ne_zero).mp h0
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    rw [measure_sdiff_null (rvachevMeasure_finite_eq_zero F
      (Polynomial.finite_setOf_isRoot hpne))]
    rw [rvachevMeasure_Ioo_eq_one F hF]
    exact zero_lt_one

/-- The Hankel determinants `h_n`. -/
noncomputable def hankelDet (F : BoundedFabius) (n : ℕ) : ℝ :=
  (momentHankel F n).det

/-- The zeroth Hankel determinant is `1`. -/
@[simp] theorem hankelDet_zero (F : BoundedFabius) :
    hankelDet F 0 = 1 := by
  simp [hankelDet]

/-- **Every Hankel determinant of the up-measure is positive.** -/
theorem hankelDet_pos (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    0 < hankelDet F n :=
  (momentHankel_posDef F hF n).det_pos

/-- The Jacobi recurrence ratios `a_n = h_{n+1}/h_n`, well-defined by
Hankel positivity. -/
noncomputable def hankelRatio (F : BoundedFabius) (n : ℕ) : ℝ :=
  hankelDet F (n + 1) / hankelDet F n

/-- **The Jacobi ratios are positive.** -/
theorem hankelRatio_pos (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) : 0 < hankelRatio F n :=
  div_pos (hankelDet_pos F hF (n + 1)) (hankelDet_pos F hF n)

end Fabius
