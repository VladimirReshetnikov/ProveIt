import Surreal.Surcomplex.HahnValuation
import Surreal.Surcomplex.Leading

/-!
# Leading data of actual complex Hahn evaluation

The actual complex Hahn embedding preserves every monomial and ordinary
complex constant. Scaling a nonzero series by its least exponent produces
an order-zero series whose constant coefficient is its leading coefficient.
The proved standard-part compatibility therefore identifies the native Hahn
leading coefficient with the actual surcomplex one.

These are the normal-form interpretations of the leading data in
`a:eq:valuation` and the decomposition preceding `a:eq:modulusleading`.
The results allow arbitrary small ordered exponent groups and infinite Hahn
supports; no divisibility assumption is used. Zero is included in all
coefficient and monomial identities.
-/

universe u v

namespace Surreal.Surcomplex

open Foundations

noncomputable section

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

/-- Every complex Hahn monomial evaluates to its prescribed actual coefficient and scale. -/
@[simp] theorem hahnEmbedding_single (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (a : Γ) (c : ℂ) :
    hahnEmbedding e he (_root_.HahnSeries.single a c) = ofComplex c * tMonomial (e a) := by
  have hs : (_root_.HahnSeries.single a c : _root_.HahnSeries Γ ℂ) =
      Surreal.HahnSeries.realComplexHahnEquiv
        ⟨_root_.HahnSeries.single a c.re, _root_.HahnSeries.single a c.im⟩ := by
    apply _root_.HahnSeries.ext
    funext b
    by_cases hb : b = a
    · subst b
      simp only [_root_.HahnSeries.coeff_single_same, Surreal.HahnSeries.coeff_realComplexHahnEquiv]
    · simp only [_root_.HahnSeries.coeff_single_of_ne hb,
        Surreal.HahnSeries.coeff_realComplexHahnEquiv]
      rfl
  rw [hs, hahnEmbedding_realComplexHahnEquiv]
  apply ext
  · change SignSequence.hahnEmbedding e he (_root_.HahnSeries.single a c.re) =
      (ofComplex c * tMonomial (e a)).re
    rw [mul_re, ofComplex_re, ofComplex_im]
    change _ = SignSequence.ofReal c.re * SignSequence.tMonomial (e a) -
      SignSequence.ofReal c.im * 0
    rw [SignSequence.hahnEmbedding_single, mul_zero, sub_zero]
  · change SignSequence.hahnEmbedding e he (_root_.HahnSeries.single a c.im) =
      (ofComplex c * tMonomial (e a)).im
    rw [mul_im, ofComplex_re, ofComplex_im]
    change _ = SignSequence.ofReal c.re * 0 +
      SignSequence.ofReal c.im * SignSequence.tMonomial (e a)
    rw [SignSequence.hahnEmbedding_single, mul_zero, zero_add]

/-- Constant complex Hahn series retain their ordinary complex values. -/
@[simp] theorem hahnEmbedding_single_zero (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (c : ℂ) : hahnEmbedding e he (_root_.HahnSeries.single 0 c) = ofComplex c := by
  rw [hahnEmbedding_single, map_zero, tMonomial_zero, mul_one]

@[simp] theorem hahnEmbedding_C (e : Γ →+ SignSequence.{u}) (he : StrictMono e) (c : ℂ) :
    hahnEmbedding e he (_root_.HahnSeries.C c) = ofComplex c :=
  hahnEmbedding_single_zero e he c

/-- Unit-coefficient monomials agree with the actual real-axis monomial map. -/
@[simp] theorem hahnEmbedding_single_one (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (a : Γ) : hahnEmbedding e he (_root_.HahnSeries.single a 1) = tMonomial (e a) := by
  rw [hahnEmbedding_single, map_one, one_mul]

/-- Native increasing Hahn order becomes the negative actual growth exponent. -/
theorem leadingExponent_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) : leadingExponent (hahnEmbedding e he z) = -e z.order := by
  by_cases hz : z = 0
  · simp [hz]
  have hz' : hahnEmbedding e he z ≠ 0 := (map_ne_zero (hahnEmbedding e he)).mpr hz
  have hv := valuation_hahnEmbedding e he z
  rw [valuation_of_ne_zero hz', ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hz,
    WithTop.map_coe] at hv
  have h := WithTop.coe_injective hv
  change -leadingExponent (hahnEmbedding e he z) = e z.order at h
  exact neg_eq_iff_eq_neg.mp h

/-- Actual leading-scale normalization is the embedding of the shifted Hahn series. -/
theorem normalized_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) :
    normalized (hahnEmbedding e he z) =
      hahnEmbedding e he (_root_.HahnSeries.single (-z.order) 1 * z) := by
  rw [normalized, leadingExponent_hahnEmbedding, neg_neg, map_mul,
    hahnEmbedding_single_one, map_neg, tMonomial_neg, div_eq_mul_inv, mul_comm]

/-- The actual complex leading coefficient equals the least nonzero Hahn coefficient. -/
theorem leadingCoeff_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) : leadingCoeff (hahnEmbedding e he z) = z.leadingCoeff := by
  by_cases hz : z = 0
  · simp [hz]
  have ho : (_root_.HahnSeries.single (-z.order) (1 : ℂ) * z).orderTop = 0 := by
    rw [_root_.HahnSeries.orderTop_mul, _root_.HahnSeries.orderTop_single one_ne_zero,
      ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hz, ← WithTop.coe_add,
      neg_add_cancel, WithTop.coe_zero]
  rw [leadingCoeff, normalized_hahnEmbedding, standardPart_hahnEmbedding e he _ ho.ge,
    _root_.HahnSeries.coeff_single_mul, one_mul, zero_sub, neg_neg,
    _root_.HahnSeries.leadingCoeff_eq]

/-- Removing the actual leading term removes precisely the native leading Hahn monomial. -/
theorem leadingTerm_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) :
    leadingTerm (hahnEmbedding e he z) =
      hahnEmbedding e he (_root_.HahnSeries.single z.order z.leadingCoeff) := by
  rw [leadingTerm, leadingExponent_hahnEmbedding, neg_neg, leadingCoeff_hahnEmbedding,
    hahnEmbedding_single, mul_comm]

/-- Every embedded series has its native leading coefficient followed by an actual infinitesimal. -/
theorem exists_leading_error_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) :
    ∃ ε : Surcomplex.{u}, IsInfinitesimal ε ∧
      hahnEmbedding e he z = tMonomial (e z.order) * (ofComplex z.leadingCoeff + ε) := by
  simpa only [leadingExponent_hahnEmbedding, neg_neg, leadingCoeff_hahnEmbedding] using
    exists_leading_error (hahnEmbedding e he z)

/-- The leading real coefficient of the actual modulus is the norm of the native complex coefficient. -/
theorem leadingCoeff_modulus_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) :
    SignSequence.leadingCoeff (modulus (hahnEmbedding e he z)) = norm z.leadingCoeff := by
  rw [leadingCoeff_modulus, leadingCoeff_hahnEmbedding]

/-- The normal-form modulus decomposition uses the same exponent and the ordinary coefficient norm. -/
theorem exists_modulus_leading_error_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) :
    ∃ ε : SignSequence.{u}, SignSequence.IsInfinitesimal ε ∧
      modulus (hahnEmbedding e he z) =
        SignSequence.tMonomial (e z.order) * (SignSequence.ofReal (norm z.leadingCoeff) + ε) := by
  simpa only [leadingExponent_hahnEmbedding, neg_neg, leadingCoeff_hahnEmbedding] using
    exists_modulus_leading_error (hahnEmbedding e he z)

/-- For a nonzero series, deleting its leading Hahn monomial strictly increases actual valuation. -/
theorem valuation_sub_leading_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    {z : _root_.HahnSeries Γ ℂ} (hz : z ≠ 0) :
    valuation (hahnEmbedding e he z) <
      valuation (hahnEmbedding e he (z - _root_.HahnSeries.single z.order z.leadingCoeff)) := by
  rw [map_sub, ← leadingTerm_hahnEmbedding]
  exact valuation_lt_sub_leadingTerm ((map_ne_zero (hahnEmbedding e he)).mpr hz)

end

end Surreal.Surcomplex
