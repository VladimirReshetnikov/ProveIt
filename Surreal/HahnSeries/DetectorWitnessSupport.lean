import Surreal.Algebra.IntersectiveWitnessPolynomials
import Surreal.HahnSeries.PolynomialSupport
import Surreal.HahnSeries.IntersectiveDetector

/-!
# Support and degree control for detector witnesses

Proves `odg:def:prop:support` for the explicit witnesses in
`odg:def:eq:witness`. All exponents remain in the original ordered group;
only finite polynomial operations are used. Membership in the full
coefficient pullback is proved together with the support and degree bounds.
-/

namespace Surreal.HahnSeries

open IntersectivePolynomial
open scoped Pointwise

noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CommRing O]

attribute [local instance] nonpositiveSupportAlgebra

/-- The affine witness t in the support ring. -/
def detectorWitnessT (r α : K) (a : nonpositiveSupportSubring Γ K) :
    nonpositiveSupportSubring Γ K := supportPolynomialEval a (witnessTPolynomial r α)

/-- The degree-five witness s in the support ring. -/
def detectorWitnessS (r α : K) (a : nonpositiveSupportSubring Γ K) :
    nonpositiveSupportSubring Γ K := supportPolynomialEval a (witnessSPolynomial r α)

theorem detectorWitnessT_val (r α : K) (a : nonpositiveSupportSubring Γ K) :
    (detectorWitnessT r α a).val =
      _root_.HahnSeries.C r + _root_.HahnSeries.C α * a.val := by
  change ((witnessTPolynomial r α).eval₂ nonpositiveConstants a).val = _
  rw [nonpositiveSupport_eval_val]
  simp [witnessTPolynomial]

/-- The affine witness adds at most the zero exponent to the input support. -/
theorem detectorWitnessT_support (r α : K) (a : nonpositiveSupportSubring Γ K) :
    (detectorWitnessT r α a).val.support ⊆ a.val.support ∪ {0} := by
  rw [detectorWitnessT_val]
  intro g hg
  rcases _root_.HahnSeries.support_add_subset _ _ hg with hg | hg
  · exact Or.inr (_root_.HahnSeries.support_single_subset hg)
  · rw [_root_.HahnSeries.C_mul_eq_smul] at hg
    exact Or.inl (_root_.HahnSeries.support_smul_subset α a.val hg)

/-- The second witness uses only sumsets of at most five input exponents. -/
theorem detectorWitnessS_support (r α : K) (hα : α ≠ 0)
    (a : nonpositiveSupportSubring Γ K) :
    (detectorWitnessS r α a).val.support ⊆ ⋃ j ≤ 5, j • (a.val.support ∪ {0}) :=
  support_supportPolynomialEval_subset (witnessSPolynomial r α) a 5
    (witnessSPolynomial_natDegree r α hα).le

/-- For nonconstant input, the affine witness has the same omega-degree. -/
theorem detectorWitnessT_degree (r α : K) (hα : α ≠ 0)
    (a : nonpositiveSupportSubring Γ K)
    (ha : a ≠ nonpositiveConstants (nonpositiveConstantCoeff a)) :
    nonpositiveDegree (detectorWitnessT r α a) = nonpositiveDegree a := by
  have hd := witnessTPolynomial_natDegree r α hα
  have hp : witnessTPolynomial r α ≠ 0 := by intro hz; simp [hz] at hd
  change nonpositiveDegree ((witnessTPolynomial r α).eval₂ nonpositiveConstants a) = _
  rw [nonpositiveDegree_eval _ hp a ha, hd, one_nsmul]

/-- For nonconstant input, the second witness has five times its omega-degree. -/
theorem detectorWitnessS_degree (r α : K) (hα : α ≠ 0)
    (a : nonpositiveSupportSubring Γ K)
    (ha : a ≠ nonpositiveConstants (nonpositiveConstantCoeff a)) :
    nonpositiveDegree (detectorWitnessS r α a) = 5 • nonpositiveDegree a := by
  have hd := witnessSPolynomial_natDegree r α hα
  have hp : witnessSPolynomial r α ≠ 0 := by intro hz; simp [hz] at hd
  change nonpositiveDegree ((witnessSPolynomial r α).eval₂ nonpositiveConstants a) = _
  rw [nonpositiveDegree_eval _ hp a ha, hd]

/-- The detector equation together with precisely the source support and degree bounds. -/
structure DetectorWitnessControl (a s t : nonpositiveSupportSubring Γ K) : Prop where
  equation : a * s = value t
  support_t : t.val.support ⊆ a.val.support ∪ {0}
  support_s : s.val.support ⊆ ⋃ j ≤ 5, j • (a.val.support ∪ {0})
  degrees : a ≠ nonpositiveConstants (nonpositiveConstantCoeff a) →
    nonpositiveDegree t = nonpositiveDegree a ∧ nonpositiveDegree s = 5 • nonpositiveDegree a

/-- The explicit polynomial witnesses have the required control for every nonzero slope. -/
theorem explicit_detectorWitnessControl (r α : K) (hr : r ^ 2 = 13) (hα : α ≠ 0)
    (a : nonpositiveSupportSubring Γ K) :
    DetectorWitnessControl a (detectorWitnessS r α a) (detectorWitnessT r α a) where
  equation := witnessPolynomials_identity r α hr a
  support_t := detectorWitnessT_support r α a
  support_s := detectorWitnessS_support r α hα a
  degrees ha := ⟨detectorWitnessT_degree r α hα a ha, detectorWitnessS_degree r α hα a ha⟩

/-- Ordinary modular values produce controlled witnesses inside the full coefficient pullback. -/
theorem detector_certificate_control (i : O →+* K) (hi : Function.Injective i)
    (hno : ∀ b : O, value b ≠ 0)
    (hmod : ∀ c : O, c ≠ 0 → ∃ b d : O, value b = c * d)
    (r : K) (hr : r ^ 2 = 13) (a : coefficientRestrictedSubring (Γ := Γ) i)
    (ha : nonpositiveConstantCoeff a.val ≠ 0) :
    ∃ s t : coefficientRestrictedSubring (Γ := Γ) i,
      DetectorWitnessControl a.val s.val t.val := by
  obtain ⟨c, hc⟩ := a.property
  have hc' : i c ≠ 0 := hc ▸ ha
  have hc0 : c ≠ 0 := by intro hz; exact hc' (by rw [hz, map_zero])
  obtain ⟨b, d, hbd⟩ := hmod c hc0
  let α : K := (i b - r) / i c
  have hα : α ≠ 0 := witness_slope_ne_zero i hi hno r hr b c hc'
  have hm := witnessPolynomials_augmentation
    (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := K)) i r hr b c d hc' hbd a.val hc.symm
  change nonpositiveConstantCoeff (detectorWitnessT r α a.val) = i b ∧
    nonpositiveConstantCoeff (detectorWitnessS r α a.val) = i d ∧ _ at hm
  refine ⟨⟨detectorWitnessS r α a.val, ⟨d, hm.2.1.symm⟩⟩,
    ⟨detectorWitnessT r α a.val, ⟨b, hm.1.symm⟩⟩, ?_⟩
  exact explicit_detectorWitnessControl r α hr hα a.val

/-- The full real Hahn pullback has certificates with the printed support and degree bounds. -/
theorem real_detector_certificate_control
    (a : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ))
    (ha : nonpositiveConstantCoeff a.val ≠ 0) :
    ∃ s t : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ),
      DetectorWitnessControl a.val s.val t.val :=
  detector_certificate_control (Int.castRingHom ℝ) Int.cast_injective integer_value_ne_zero
    integer_modular_value (Real.sqrt 13) (by norm_num [Real.sq_sqrt]) a ha

/-- The same controlled certificates work for the full Gaussian Hahn pullback. -/
theorem complex_detector_certificate_control
    (a : coefficientRestrictedSubring (Γ := Γ) GaussianInt.toComplex)
    (ha : nonpositiveConstantCoeff a.val ≠ 0) :
    ∃ s t : coefficientRestrictedSubring (Γ := Γ) GaussianInt.toComplex,
      DetectorWitnessControl a.val s.val t.val := by
  apply detector_certificate_control GaussianInt.toComplex GaussianInt.toComplex_injective
    gaussian_value_ne_zero gaussian_modular_value (Real.sqrt 13 : ℂ) ?_ a ha
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)

end
end Surreal.HahnSeries
