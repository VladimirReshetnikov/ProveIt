import GRHArticle.SingularModuli.ClassPolynomialQEnclosure
import GRHArticle.SingularModuli.ClassPolynomialTruncation

/-!
# Certified boxes for the modular invariant at quartic CM inputs

The finite Eisenstein and Euler evaluations share their powers of the
q-parameter. The analytic tail bounds widen the boxes before taking the
quotient defining the modular invariant.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators

private structure PartialBoxes where
  eisenstein : RationalComplexBox
  eulerProduct : RationalComplexBox
  qPower : RationalComplexBox

private def oneBox : RationalComplexBox := RationalComplexBox.point 1 0

private def partialBoxes (A : RationalComplexBox) : ℕ → PartialBoxes
  | 0 => ⟨oneBox, oneBox, oneBox⟩
  | n + 1 =>
    let prev := partialBoxes A n
    let power := prev.qPower.mul A
    let term := RationalComplexBox.point (240 * (ArithmeticFunction.sigma 3 (n + 1) : ℚ)) 0
    ⟨prev.eisenstein.add (term.mul power), prev.eulerProduct.mul (oneBox.sub power), power⟩

private theorem oneBox_contains : oneBox.Contains 1 := by
  simp [oneBox, RationalComplexBox.Contains, RationalComplexBox.point,
    RationalInterval.Contains, RationalInterval.point]

private theorem contains_partialBoxes {A : RationalComplexBox} {q : ℂ} (hq : A.Contains q)
    (n : ℕ) :
    ((partialBoxes A n).eisenstein.Contains
      (1 + 240 * ∑ k ∈ Finset.range n, (ArithmeticFunction.sigma 3 (k + 1) : ℂ) * q ^ (k + 1))) ∧
    ((partialBoxes A n).eulerProduct.Contains (∏ k ∈ Finset.range n, (1 - q ^ (k + 1)))) ∧
    ((partialBoxes A n).qPower.Contains (q ^ n)) := by
  induction n with
  | zero => simpa only [partialBoxes, Finset.sum_range_zero, mul_zero, add_zero,
      Finset.prod_range_zero, pow_zero] using ⟨oneBox_contains, oneBox_contains, oneBox_contains⟩
  | succ n ih =>
    obtain ⟨hE, hP, hp⟩ := ih
    have hpow := RationalComplexBox.contains_mul hp hq
    have hterm : (RationalComplexBox.point (240 * (ArithmeticFunction.sigma 3 (n + 1) : ℚ)) 0).Contains
        (240 * (ArithmeticFunction.sigma 3 (n + 1) : ℂ)) := by
      have h := RationalComplexBox.contains_point
        (240 * (ArithmeticFunction.sigma 3 (n + 1) : ℚ)) 0
      convert h using 1
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    refine ⟨?_, ?_, ?_⟩
    · have h := RationalComplexBox.contains_add hE (RationalComplexBox.contains_mul hterm hpow)
      rw [Finset.sum_range_succ]
      have hsum : 1 + 240 * ((∑ k ∈ Finset.range n,
          (ArithmeticFunction.sigma 3 (k + 1) : ℂ) * q ^ (k + 1)) +
            (ArithmeticFunction.sigma 3 (n + 1) : ℂ) * q ^ (n + 1)) =
          1 + 240 * (∑ k ∈ Finset.range n,
            (ArithmeticFunction.sigma 3 (k + 1) : ℂ) * q ^ (k + 1)) +
            240 * (ArithmeticFunction.sigma 3 (n + 1) : ℂ) * (q ^ n * q) := by
        rw [pow_succ]
        ring
      rw [hsum]
      exact h
    · rw [Finset.prod_range_succ]
      exact RationalComplexBox.contains_mul hP
        (RationalComplexBox.contains_sub oneBox_contains (by simpa only [pow_succ] using hpow))
    · simpa only [partialBoxes, pow_succ] using hpow

private def truncationRadius : ℚ := 1 / 10 ^ 200

private theorem eisensteinError_le_radius :
    (960 : ℝ) * 165 ^ 3 / 200 ^ 165 ≤ (truncationRadius : ℝ) := by
  norm_num [truncationRadius]

private theorem eulerError_le_radius :
    (8 : ℝ) / 200 ^ 165 ≤ (truncationRadius : ℝ) := by
  norm_num [truncationRadius]

private def jNumeratorBox (A : RationalComplexBox) : RationalComplexBox :=
  ((partialBoxes A 164).eisenstein.widen truncationRadius).pow 3

private def jDenominatorBox (A : RationalComplexBox) : RationalComplexBox :=
  A.mul (((partialBoxes A 164).eulerProduct.widen truncationRadius).pow 24)

def modularInvariantBox (A : RationalComplexBox) : RationalComplexBox :=
  (jNumeratorBox A).mul (jDenominatorBox A).inv

def modularInvariantBoxDenominatorPositive (A : RationalComplexBox) : Prop :=
  0 < (jDenominatorBox A).normSq.lo

instance (A : RationalComplexBox) : Decidable (modularInvariantBoxDenominatorPositive A) := by
  unfold modularInvariantBoxDenominatorPositive
  infer_instance

/-- A certified box for a reduced CM input, given its q-box and a positive lower
bound on the squared norm of the denominator box. -/
theorem modularInvariantBox_contains {D : ℕ+} {f : FormCoefficients} (hf : f ∈ reducedForms D)
    {A : RationalComplexBox}
    (hq : A.Contains (Function.Periodic.qParam 1 (quadraticPoint D f.a f.b)))
    (hpos : modularInvariantBoxDenominatorPositive A) :
    (modularInvariantBox A).Contains (modularInvariant (quadraticPoint D f.a f.b)) := by
  let z := quadraticPoint D f.a f.b
  let q := Function.Periodic.qParam 1 z
  obtain ⟨hE, hP, _⟩ := contains_partialBoxes hq 164
  obtain ⟨hEerr, hPerr⟩ := classPolynomial_truncation_bounds D f hf
  have hE' := RationalComplexBox.contains_widen hE (hEerr.trans eisensteinError_le_radius)
  have hP' := RationalComplexBox.contains_widen hP (hPerr.le.trans eulerError_le_radius)
  have hden := RationalComplexBox.contains_mul hq (RationalComplexBox.contains_pow hP' 24)
  have hn := RationalComplexBox.contains_pow hE' 3
  have hi := RationalComplexBox.contains_inv hpos hden
  have hq₁ : ‖q‖ < 1 := Function.Periodic.norm_qParam_lt_one (by norm_num) z.im_pos
  have hmult : Multipliable (fun k : ℕ ↦ 1 - q ^ (k + 1)) := by
    have h : Summable (fun k : ℕ ↦ ‖-(q ^ (k + 1))‖) := by
      simp only [norm_neg, pow_succ, norm_mul, norm_pow]
      exact (summable_geometric_of_lt_one (norm_nonneg _) hq₁).mul_right _
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable h
  unfold modularInvariant
  rw [ModularForm.discriminant_eq_q_prod, hmult.tprod_pow, div_eq_mul_inv]
  exact RationalComplexBox.contains_mul hn hi

end GRHArticle.SingularModuli
