import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaAllDegreeCoefficientStability
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaRadiusCoefficientName

/-!
# All original Gamma coefficient names at every positive common radius

The actual padded head has the unchanged original coefficient norm.
Original finite Cauchy estimates therefore retain the already proved
numerical modulus at every degree. Exact reader preservation returns
to the SAME original unpadded coefficient. The SAME packed-radius name
program now has genuine pointCN under R>=1 alone; no head-degree guard
or replacement sampler remains.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaAllDegreeCoefficientVariation

open_ipra
open GaussianGammaAllDegreeCoefficientStability (paddedHead headDegree)
open GaussianGammaFixedCoefficientVariation (exponential exponentialFactor rowFactor modulus headBudget exponential_error_norm subst_exponential subst_rowFactor)
open GaussianGammaFiniteCoefficientStability (fixedCoefficient)
open GaussianGammaInputPrecisionNorm (radiusNumerator radiusDenominator denominator_positive)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalL1 (qL1)
open GaussianCoefficientL1 (coefficientNorm qL1_congr)
open GaussianRationalSyntheticBounds (natCode)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalLowCoefficientConvolution (exponent_inside)
open GaussianEuclideanDistanceName (fraction pointCN)
open RationalArithmetic (multiply)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem padded_head_length (R e : PTm n) : Γ ⊢[PRAAx] length (paddedHead R e) ≐ succ (headDegree R e) :=
  GaussianPolynomialProductLeftPadding.factor_length _ _ _ (GaussianGammaEulerHeadPolynomial.polynomial_length _)

theorem padded_head_norm (R e : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (paddedHead R e)) (natCode (headBudget R)) :=
  RationalArgmin.rationalLE_congr (GaussianPolynomialNormBuffers.norm_padding _ _).eqSymm (.eqRefl _)
    (GaussianGammaFixedCoefficientVariation.head_norm R hR)

theorem row_error (p q R e i : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub
      (GaussianRationalLowCoefficientConvolution.term (paddedHead R e) (exponential p R e)
        (headDegree R e) (e*degree e) e i)
      (GaussianRationalLowCoefficientConvolution.term (paddedHead R e) (exponential q R e)
        (headDegree R e) (e*degree e) e i)))
      (fraction (rowFactor R e*radiusNumerator p q) (radiusDenominator p q)) := by
  let j := LeanProofs.IPRA.PTm.monus (headDegree R e) i
  let k := LeanProofs.IPRA.PTm.monus (e*degree e) (LeanProofs.IPRA.PTm.monus e i)
  have hDegree := GaussianGammaFiniteCoefficientStability.output_degree_bound (Γ := Γ) e e e (le_refl e)
  have hf := GaussianRationalMonicReconstruction.monus_le_left (Γ := Γ) e i
  have hi := le_trans hf hDegree
  have codes := qsub_congr (Γ := Γ) (exponent_inside (exponential p R e) (e*degree e) _ hi)
    (exponent_inside (exponential q R e) (e*degree e) _ hi)
  have expBound := RationalArgmin.rationalLE_congr (qL1_congr codes) (.eqRefl _)
    (exponential_error_norm p q R e _ hR hf)
  have hEntry : Γ ⊢[PRAAx] lt j (length (paddedHead R e)) :=
    lt_congr (.eqRefl _) (padded_head_length R e).eqSymm
      ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))
  have headBound := RationalArgmin.transitive (GaussianCoefficientNormEntries.coefficient_entry_bound _ _ hEntry) (padded_head_norm R e hR)
  have product := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply (Γ := Γ)
    (entry (paddedHead R e) j) (qsub (entry (exponential p R e) k) (entry (exponential q R e) k)))
      (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (GaussianRationalL1.qL1_nonnegative _)
        (GaussianRationalSyntheticBounds.natCode_nonnegative _) headBound expBound)
  have code : Γ ⊢[PRAAx] multiply (natCode (headBudget R))
      (fraction (exponentialFactor R e*radiusNumerator p q) (radiusDenominator p q)) ≐
      fraction (rowFactor R e*radiusNumerator p q) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by unfold rowFactor; ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr
    (qL1_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _)).eqSymm code product

theorem cauchy_error (p q R e : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub
      (GaussianRationalLowCoefficientConvolution.cauchySum (paddedHead R e) (exponential p R e)
        (headDegree R e) (e*degree e) e)
      (GaussianRationalLowCoefficientConvolution.cauchySum (paddedHead R e) (exponential q R e)
        (headDegree R e) (e*degree e) e)))
      (fraction (modulus R e*radiusNumerator p q) (radiusDenominator p q)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have rows : Γ ⊢[PRAAx] GaussianFiniteSumL1Variation.termsError
      GaussianRationalLowCoefficientConvolution.termBody GaussianRationalLowCoefficientConvolution.termBody (succ e)
      (GaussianRationalLowCoefficientConvolution.data (paddedHead R e) (exponential p R e) (headDegree R e) (e*degree e) e)
      (GaussianRationalLowCoefficientConvolution.data (paddedHead R e) (exponential q R e) (headDegree R e) (e*degree e) e)
      (fraction (rowFactor R e*radiusNumerator p q) (radiusDenominator p q)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (succ e)) :: Γ.map Fm.shift
    have codes := qsub_congr (Γ := Δ)
      (GaussianRationalLowCoefficientConvolution.term_at (paddedHead (Syn.shift R) (Syn.shift e))
        (exponential (Syn.shift p) (Syn.shift R) (Syn.shift e)) (headDegree (Syn.shift R) (Syn.shift e)) (Syn.shift e*degree (Syn.shift e)) (Syn.shift e) (var 0))
      (GaussianRationalLowCoefficientConvolution.term_at (paddedHead (Syn.shift R) (Syn.shift e))
        (exponential (Syn.shift q) (Syn.shift R) (Syn.shift e)) (headDegree (Syn.shift R) (Syn.shift e)) (Syn.shift e*degree (Syn.shift e)) (Syn.shift e) (var 0))
    simpa only [Δ,GaussianFiniteSumL1Variation.termsError,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,
      GaussianGammaAllDegreeCoefficientStability.subst_paddedHead,GaussianGammaAllDegreeCoefficientStability.subst_headDegree,subst_exponential,PTm.subst_mul,PTm.subst_succ,PTm.subst_zero,
      GaussianGammaReciprocalDegreeCells.subst_degree,GaussianEuclideanDistanceName.subst_fraction,subst_rowFactor,
      GaussianGammaInputPrecisionNorm.subst_radiusNumerator,GaussianGammaInputPrecisionNorm.subst_radiusDenominator] using
      RationalArgmin.rationalLE_congr (qL1_congr codes).eqSymm (.eqRefl _) (row_error (Syn.shift p) (Syn.shift q) (Syn.shift R) (Syn.shift e) (var 0) hs.wk)
  have sum := GaussianFiniteSumL1Variation.sum_error _ _ _ _ _ _ rows
  have code : Γ ⊢[PRAAx] multiply (natCode (succ e)) (fraction (rowFactor R e*radiusNumerator p q) (radiusDenominator p q)) ≐
      fraction (modulus R e*radiusNumerator p q) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by unfold modulus; ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) code sum

theorem fixed_coefficient_distance (p q R e : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    distanceBounded (fixedCoefficient p R e) (fixedCoefficient q R e)
      (modulus R e*radiusNumerator p q) (radiusDenominator p q) := by
  have hD := GaussianGammaFiniteCoefficientStability.output_degree_bound (Γ := Γ) e e e (le_refl e)
  have left := (GaussianGammaAllDegreeCoefficientStability.padding_reader (Γ := Γ) p R e e e (le_refl e)).eqSymm.eqTrans
    (GaussianRationalLowCoefficientConvolution.product_exponent (paddedHead R e) (exponential p R e)
      (headDegree R e) (e*degree e) e (le_add_right e _) hD)
  have right := (GaussianGammaAllDegreeCoefficientStability.padding_reader (Γ := Γ) q R e e e (le_refl e)).eqSymm.eqTrans
    (GaussianRationalLowCoefficientConvolution.product_exponent (paddedHead R e) (exponential q R e)
      (headDegree R e) (e*degree e) e (le_add_right e _) hD)
  exact GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (denominator_positive p q)
    (RationalArgmin.rationalLE_congr (qL1_congr (qsub_congr left right)).eqSymm (.eqRefl _) (cauchy_error p q R e hR))

theorem later_distance (s t a b R e : PTm n) (ha : Γ ⊢[PRAAx] le s a) (hb : Γ ⊢[PRAAx] le t b)
    (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    distanceBounded (fixedCoefficient a R e) (fixedCoefficient b R e)
      (modulus R e*radiusNumerator s t) (radiusDenominator s t) := by
  have sa : Γ ⊢[PRAAx] le (unit s) (unit a) := GaussianFactorBudget.power_monotone_length two s a (le_succ_self one) ha
  have tb : Γ ⊢[PRAAx] le (unit t) (unit b) := GaussianFactorBudget.power_monotone_length two t b (le_succ_self one) hb
  have first := mul_le_mul_right (unit a*unit s) tb
  have second := mul_le_mul_right (unit b*unit t) sa
  have base : Γ ⊢[PRAAx] le ((unit a+unit b)*(unit s*unit t)) ((unit s+unit t)*(unit a*unit b)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first second)
  have budget : Γ ⊢[PRAAx] le
      ((modulus R e*radiusNumerator a b)*radiusDenominator s t)
      ((modulus R e*radiusNumerator s t)*radiusDenominator a b) :=
    le_congr (by unfold radiusNumerator radiusDenominator; ipra_ring)
      (by unfold radiusNumerator radiusDenominator; ipra_ring) (mul_le_mul_right (modulus R e) base)
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (denominator_positive a b) (denominator_positive s t) budget (fixed_coefficient_distance a b R e hR)

theorem cofinal_regularity (p q R e : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaRadiusCoefficientName.rawValue p R e) (GaussianGammaRadiusCoefficientName.rawValue q R e)
      (modulus R e*(unit p+unit q)) (unit p*unit q) := by
  have pc := le_trans (le_add_right p e) (GaussianGammaCofinalCoefficientName.coefficient_precision_cofinal (Γ := Γ) (p+e) R)
  have qc := le_trans (le_add_right q e) (GaussianGammaCofinalCoefficientName.coefficient_precision_cofinal (Γ := Γ) (q+e) R)
  exact distance_congr (GaussianGammaAllDegreeCoefficientStability.cofinal_observation_fixed p R e).eqSymm
    (GaussianGammaAllDegreeCoefficientStability.cofinal_observation_fixed q R e).eqSymm (.eqRefl _) (.eqRefl _)
      (later_distance p q _ _ R e pc qc hR)

theorem raw_regular (R e : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular GaussianGammaRadiusCoefficientName.rawF (modulus R e) (GaussianGammaRadiusCoefficientName.rawData R e) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift R)) := by
    simpa [Fm.shift,Syn.shift] using hR.shift.shift
  refine .allI (.allI ?_)
  have actual := distance_congr (GaussianGammaRadiusCoefficientName.raw_at (var 1) _ _).eqSymm
    (GaussianGammaRadiusCoefficientName.raw_at (var 0) _ _).eqSymm (.eqRefl _) (.eqRefl _)
      (cofinal_regularity (var 1) (var 0) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift e)) hs)
  simpa only [GaussianFastValueCut.regular,Syn.shift,GaussianGammaRadiusCoefficientName.subst_rawData,
    GaussianGammaFixedCoefficientVariation.subst_modulus,unit] using actual

theorem name_regular (R e : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    pointCN GaussianGammaRadiusCoefficientName.nameF (GaussianGammaRadiusCoefficientName.data R e) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regular R e hR)

theorem original_all_degree_fixed_Gamma_coefficient_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ distanceBounded (fixedCoefficient (var 0) (var 2) (var 3)) (fixedCoefficient (var 1) (var 2) (var 3))
      (modulus (var 2) (var 3)*radiusNumerator (var 0) (var 1)) (radiusDenominator (var 0) (var 1))) :=
  closeUniv 4 (.impI (fixed_coefficient_distance _ _ _ _ Prf.hyp0))
theorem original_all_degree_positive_radius_Gamma_coefficient_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ pointCN GaussianGammaRadiusCoefficientName.nameF (GaussianGammaRadiusCoefficientName.data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaAllDegreeCoefficientVariation
