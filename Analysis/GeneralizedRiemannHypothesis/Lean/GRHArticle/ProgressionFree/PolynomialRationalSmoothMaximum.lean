import GRHArticle.ProgressionFree.PolynomialRationalRatios
import GRHArticle.ProgressionFree.PolynomialSmoothOptimization

/-!
# Exact smooth-ball optima for rational-function ratios

Check midpoint products by coefficient convolution and scalar proportionality
by a finite field search. This enumerates the finite optimizers even when
two distinct monic polynomials of the same degree have a nonconstant ratio.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

private def scalarTest (a b : Coefficients F n) : Bool :=
  decide (∃ t ∈ (Finset.univ : Finset F), ∀ i ∈ (Finset.univ : Finset (Fin n)), b i = a i * t)

private def midpointTest (a b c : Coefficients F n) : Bool :=
  (List.range (2*n)).all fun i ↦ decide (vectorProductCoeff a c i = vectorProductCoeff b b i)

private def rationalVectorTest (B : Finset (Coefficients F n)) : Bool :=
  decide (∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    midpointTest a b c = true → scalarTest a b = true)

omit [Fintype F] [DecidableEq F] in
private theorem vectorProductCoeff_eq (a b : Coefficients F n) (i : ℕ) :
    vectorProductCoeff a b i = (vectorPolynomial n a * vectorPolynomial n b).coeff i := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [vectorPolynomial_coeff,vectorProductCoeff]

omit [Fintype F] [DecidableEq F] in
private theorem vector_midpoint_iff (a b c : Coefficients F n) :
    (∀ i ∈ Finset.range (2*n), vectorProductCoeff a c i = vectorProductCoeff b b i) ↔
      vectorPolynomial n a * vectorPolynomial n c = vectorPolynomial n b * vectorPolynomial n b := by
  simp only [vectorProductCoeff_eq]
  refine ⟨fun h ↦ Polynomial.ext fun i ↦ ?_,fun h i _ ↦ congrArg (fun f : F[X] ↦ f.coeff i) h⟩
  by_cases hi : i < 2*n
  · exact h i (mem_range.mpr hi)
  · have hz (u v : Coefficients F n) : (vectorPolynomial n u * vectorPolynomial n v).coeff i = 0 := by
      rw [← vectorProductCoeff_eq, vectorProductCoeff]
      apply sum_eq_zero
      intro j hj
      have := mem_range.mp hj
      by_cases h : j < n
      · rw [show vectorCoeff v (i-j) = 0 by exact dif_neg (by omega), mul_zero]
      · rw [show vectorCoeff u j = 0 by exact dif_neg h,zero_mul]
    rw [hz a c,hz b b]

omit [Fintype F] [DecidableEq F] in
private theorem vector_constant_ratio_iff (a b : Coefficients F n) (t : F) :
    (∀ i, b i = a i * t) ↔ vectorPolynomial n b = vectorPolynomial n a * C t := by
  constructor
  · intro h
    apply Polynomial.ext
    intro i
    simp only [coeff_mul_C,vectorPolynomial_coeff,vectorCoeff]
    split <;> simp_all
  · intro h i
    have he := congrArg (fun f : F[X] ↦ f.coeff i.val) h
    simpa only [coeff_mul_C,vectorPolynomial_coeff,vectorCoeff,dif_pos i.is_lt] using he

private theorem rationalVectorTest_iff (B : Finset (Coefficients F n)) :
    rationalVectorTest B = true ↔ RationalFunctionRatioThreeGPFree ((B.map (vectorPolynomial n)) : Set F[X]) := by
  rw [rationalVectorTest,decide_eq_true_eq]
  have hm (x y z : Coefficients F n) : midpointTest x y z = true ↔
      ∀ i ∈ Finset.range (2*n), vectorProductCoeff x z i = vectorProductCoeff y y i := by
    simp only [midpointTest,List.all_eq_true,List.mem_range,Finset.mem_range,decide_eq_true_eq]
  simp only [hm, scalarTest,decide_eq_true_eq, Finset.mem_univ, true_implies, true_and]
  have hz (a : Coefficients F n) : vectorPolynomial n a ≠ 0 ↔ a ≠ 0 := by
    rw [← vectorPolynomial_zero (F := F) (n := n), (vectorPolynomial n).injective.ne_iff]
  constructor
  · intro h a b c ha hb hc haB hbB hcB he
    obtain ⟨x,hx,rfl⟩ := mem_map.mp haB
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hbB
    obtain ⟨z,hz',rfl⟩ := mem_map.mp hcB
    obtain ⟨t,ht⟩ := h x hx y hy z hz' ((hz x).mp ha) ((hz y).mp hb) ((hz z).mp hc)
      ((vector_midpoint_iff x y z).mpr he)
    exact ⟨t,(vector_constant_ratio_iff x y t).mp ht⟩
  · intro h a ha b hb c hc ha₀ hb₀ hc₀ he
    obtain ⟨t,ht⟩ := h ((hz a).mpr ha₀) ((hz b).mpr hb₀) ((hz c).mpr hc₀)
      (mem_map.mpr ⟨a,ha,rfl⟩) (mem_map.mpr ⟨b,hb,rfl⟩) (mem_map.mpr ⟨c,hc,rfl⟩)
      ((vector_midpoint_iff a b c).mp he)
    exact ⟨t,(vector_constant_ratio_iff a b t).mpr ht⟩

/-- Finite exhaustive search for the article's rational-ratio smooth maximum. -/
def rationalFunctionSmoothMaximum (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (T t : ℕ) : ℕ := polynomialSmoothMaximumWith F T t rationalVectorTest

theorem le_rationalFunctionSmoothMaximum {T t : ℕ} {B : Finset F[X]}
    (hB : B ⊆ polynomialSmoothBall F T t) (hfree : RationalFunctionRatioThreeGPFree (B : Set F[X])) :
    B.card ≤ rationalFunctionSmoothMaximum F T t :=
  le_polynomialSmoothMaximumWith rationalVectorTest RationalFunctionRatioThreeGPFree rationalVectorTest_iff hB hfree

theorem exists_rationalFunctionSmoothMaximum (T t : ℕ) :
    ∃ B : Finset F[X], B ⊆ polynomialSmoothBall F T t ∧ RationalFunctionRatioThreeGPFree (B : Set F[X]) ∧
      B.card = rationalFunctionSmoothMaximum F T t :=
  exists_polynomialSmoothMaximumWith T t rationalVectorTest RationalFunctionRatioThreeGPFree rationalVectorTest_iff
    (by intro a b c _ _ _ ha; exact ha.elim)

end GRHArticle.ProgressionFree
