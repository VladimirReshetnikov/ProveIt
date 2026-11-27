import GRHArticle.ProgressionFree.PolynomialRationalSmoothMaximum
import GRHArticle.ProgressionFree.PolynomialReplacementCount

/-!
# Rational-function progressions in polynomial rough fibers

Squarefree rough factors have only zero-one multiplicities. A midpoint
identity forces all three rough multisets to agree even when the step
is signed. The smooth rule may depend on this common rough factor.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid

variable {F : Type*} [Field F]

theorem RationalFunctionRatioThreeGPFree.mono {A B : Set F[X]}
    (h : RationalFunctionRatioThreeGPFree B) (hs : A ⊆ B) : RationalFunctionRatioThreeGPFree A :=
  fun _ _ _ ha hb hc ha' hb' hc' ↦ h ha hb hc (hs ha') (hs hb') (hs hc')

theorem RationalFunctionRatioThreeGPFree.polynomial {A : Set F[X]}
    (h : RationalFunctionRatioThreeGPFree A) : PolynomialRatioThreeGPFree A := by
  intro f r hf hr htriple
  have hr₀ : r ≠ 0 := by rintro rfl; simp at hr
  obtain ⟨t,ht⟩ := h hf (mul_ne_zero hf hr₀) (mul_ne_zero (mul_ne_zero hf hr₀) hr₀)
    htriple.1 htriple.2.1 htriple.2.2 (by ring)
  have he := mul_left_cancel₀ hf ht
  simp [he] at hr

/-- Pulling a rational-ratio admissible set back along any nonzero
polynomial dilation preserves admissibility. -/
theorem RationalFunctionRatioThreeGPFree.mul_preimage {A : Set F[X]}
    (h : RationalFunctionRatioThreeGPFree A) {u : F[X]} (hu : u ≠ 0) :
    RationalFunctionRatioThreeGPFree ((u * ·) ⁻¹' A) := by
  intro a b c ha hb hc ha' hb' hc' he
  have hm : (u*a)*(u*c) = (u*b)*(u*b) := by
    calc
      _ = (u*u)*(a*c) := by ring
      _ = (u*u)*(b*b) := by rw [he]
      _ = _ := by ring
  obtain ⟨t,ht⟩ := h (mul_ne_zero hu ha) (mul_ne_zero hu hb) (mul_ne_zero hu hc) ha' hb' hc' hm
  exact ⟨t,mul_left_cancel₀ hu (ht.trans (mul_assoc _ _ _))⟩

private theorem same_squarefree_rough_parts (T : ℕ) {a b c : F[X]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : a*c = b*b)
    (ha' : Squarefree (polynomialRoughPart T a)) (hb' : Squarefree (polynomialRoughPart T b))
    (hc' : Squarefree (polynomialRoughPart T c)) :
    polynomialRoughPart T a = polynomialRoughPart T b ∧ polynomialRoughPart T b = polynomialRoughPart T c := by
  classical
  let R := polynomialRoughFactors (F := F) T
  have hmul {x y : F[X]} (hx : x ≠ 0) (hy : y ≠ 0) : R (x*y) = R x + R y := by
    simp only [R,polynomialRoughFactors,normalizedFactors_mul hx hy,Multiset.filter_add]
  have h := congrArg R he
  rw [hmul ha hc,hmul hb hb] at h
  have hcount (p : F[X]) : (R a).count p = (R b).count p ∧ (R b).count p = (R c).count p := by
    have h₁ := Multiset.nodup_iff_count_le_one.mp ((squarefree_polynomialRoughPart_iff T a).mp ha') p
    have h₂ := Multiset.nodup_iff_count_le_one.mp ((squarefree_polynomialRoughPart_iff T b).mp hb') p
    have h₃ := Multiset.nodup_iff_count_le_one.mp ((squarefree_polynomialRoughPart_iff T c).mp hc') p
    have hp := congrArg (Multiset.count p) h
    simp only [Multiset.count_add] at hp
    change (R a).count p ≤ 1 at h₁
    change (R b).count p ≤ 1 at h₂
    change (R c).count p ≤ 1 at h₃
    omega
  exact ⟨congrArg Multiset.prod (Multiset.ext.mpr (fun p ↦ (hcount p).1)),
    congrArg Multiset.prod (Multiset.ext.mpr (fun p ↦ (hcount p).2))⟩

/-- Independent rational-ratio admissible smooth rules, indexed by
squarefree monic rough part, give a globally admissible polynomial set. -/
theorem rationalFunctionRatioThreeGPFree_squarefreeFibers (T : ℕ) (H : F[X] → Set F[X])
    (hH : ∀ g, RationalFunctionRatioThreeGPFree (H g)) :
    RationalFunctionRatioThreeGPFree {f : F[X] | Squarefree (polynomialRoughPart T f) ∧
      polynomialSmoothPart T f ∈ H (polynomialRoughPart T f)} := by
  classical
  intro a b c ha hb hc ha' hb' hc' he
  obtain ⟨hab,hbc⟩ := same_squarefree_rough_parts T ha hb hc he ha'.1 hb'.1 hc'.1
  have hmul {x y : F[X]} (hx : x ≠ 0) (hy : y ≠ 0) : polynomialSmoothPart T (x*y) =
      polynomialSmoothPart T x * polynomialSmoothPart T y := by
    simp only [polynomialSmoothPart, normalizedFactors_mul hx hy, Multiset.filter_add, Multiset.prod_add]
  have h := congrArg (polynomialSmoothPart T) he
  rw [hmul ha hc,hmul hb hb] at h
  obtain ⟨t,ht⟩ := hH (polynomialRoughPart T b) (monic_polynomialSmoothPart T a).ne_zero
    (monic_polynomialSmoothPart T b).ne_zero (monic_polynomialSmoothPart T c).ne_zero
    (hab ▸ ha'.2) hb'.2 (hbc.symm ▸ hc'.2) h
  refine ⟨b.leadingCoeff / a.leadingCoeff * t,?_⟩
  have hl : a.leadingCoeff * (b.leadingCoeff / a.leadingCoeff) = b.leadingCoeff := by
    field_simp [leadingCoeff_ne_zero.mpr ha]
  calc
    b = C b.leadingCoeff * polynomialRoughPart T b * polynomialSmoothPart T b :=
      (polynomial_eq_leadingCoeff_mul_roughPart_mul_smoothPart T b).symm
    _ = (C a.leadingCoeff * polynomialRoughPart T a * polynomialSmoothPart T a) *
        C (b.leadingCoeff / a.leadingCoeff * t) := by
      rw [ht,← hab,map_mul,← congrArg C hl,map_mul]
      ring
    _ = _ := by rw [polynomial_eq_leadingCoeff_mul_roughPart_mul_smoothPart]

theorem rationalFunctionSmoothMaximum_le_polynomialSmoothMaximum [Fintype F] [DecidableEq F] (T t : ℕ) :
    rationalFunctionSmoothMaximum F T t ≤ polynomialSmoothMaximum F T t := by
  obtain ⟨B,hB,hfree,he⟩ := exists_rationalFunctionSmoothMaximum (F := F) T t
  rw [← he]
  exact le_polynomialSmoothMaximum hB hfree.polynomial

end GRHArticle.ProgressionFree
