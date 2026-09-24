import Surreal.Algebra.Geometry
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite weighted variance over the scalar field

The weighted variance identity used in the proof of
`trigonometry:thm:euler` is a polynomial identity. The division-free
form holds over every commutative ring, without positivity assumptions.
Its three-point specialization supplies the actual incentre–circumcentre
calculation without introducing a real-valued norm.
-/

namespace Surreal.Complexify

variable {F : Type*} [CommRing F]

private theorem sum_weighted_square_difference {ι : Type*} (s : Finset ι) (w x : ι → F) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) =
      2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i ^ 2) -
        2 * (∑ i ∈ s, w i * x i) ^ 2 := by
  classical
  calc
    _ = ∑ i ∈ s, (w i * x i ^ 2 * (∑ j ∈ s, w j) +
        w i * (∑ j ∈ s, w j * x j ^ 2) -
        (2 * (∑ j ∈ s, w j * x j)) * (w i * x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      ring

private theorem re_sum_weighted {ι : Type*} (s : Finset ι) (w : ι → F)
    (z : ι → Complexify F) : (∑ i ∈ s, w i • z i).re = ∑ i ∈ s, w i * (z i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, QuadraticAlgebra.re_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul,
      smul_eq_mul, ih]

private theorem im_sum_weighted {ι : Type*} (s : Finset ι) (w : ι → F)
    (z : ι → Complexify F) : (∑ i ∈ s, w i • z i).im = ∑ i ∈ s, w i * (z i).im := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, QuadraticAlgebra.im_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul,
      smul_eq_mul, ih]

/-- Finite weighted variance with an ordered-pair sum; twice the unordered-pair contribution
appears on the right. This division-free form holds in every characteristic. -/
theorem normSq_weighted_variance {ι : Type*} (s : Finset ι) (w : ι → F)
    (z : ι → Complexify F) :
    2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * normSq (z i)) =
      2 * normSq (∑ i ∈ s, w i • z i) +
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * normSq (z i - z j) := by
  simp only [normSq, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    re_sum_weighted, im_sum_weighted, mul_add, Finset.sum_add_distrib]
  rw [sum_weighted_square_difference, sum_weighted_square_difference]
  ring

/-- Three-point weighted variance, with no divisions or assumptions on the weights. -/
theorem normSq_weighted_variance_three (a b c : F) (A B C : Complexify F) :
    (a + b + c) * (a * normSq A + b * normSq B + c * normSq C) =
      normSq (a • A + b • B + c • C) + a * b * normSq (A - B) +
        a * c * normSq (A - C) + b * c * normSq (B - C) := by
  simp only [normSq, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_smul,
    QuadraticAlgebra.im_smul, smul_eq_mul]
  ring

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The squared norm of a finite weighted mean is the mean squared norm minus its pairwise
variance. The factor two accounts for the two orientations of every distinct pair. -/
theorem normSq_weighted_mean {ι : Type*} (s : Finset ι) (w : ι → K)
    (z : ι → Complexify K) (hw : (∑ i ∈ s, w i) ≠ 0) :
    normSq ((∑ i ∈ s, w i)⁻¹ • (∑ i ∈ s, w i • z i)) =
      (∑ i ∈ s, w i * normSq (z i)) / (∑ i ∈ s, w i) -
        (∑ i ∈ s, ∑ j ∈ s, w i * w j * normSq (z i - z j)) /
          (2 * (∑ i ∈ s, w i) ^ 2) := by
  rw [normSq_smul]
  have he := normSq_weighted_variance s w z
  field_simp [hw]
  linear_combination -he

end Field

end Surreal.Complexify
