import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaOriginalPrefixCoefficientNames
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaOriginalPrefixName
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalPrefixName
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Canonical Gamma coefficients reproduce the original named C19 prefix

Actual mixed coefficient comparison is accumulated in the unchanged
finite power sums. Their proved numerical clocks yield exact independent
observation equivalence of the original cofinal prefix name and the
literal finite evaluation of the canonical coefficient names. Genuine
named-rate transport retains the exact original C19 geometric tail.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPrefixCompatibility

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaOriginalC19Prefix (prefixValue)
open GaussianGammaOriginalPrefixCoefficientVariation (cap)
open GaussianGammaOriginalPrefixCoefficientNames (reader)
open GaussianGammaInputPrecisionNorm (radiusDenominator denominator_positive)
open GaussianRationalHorner (qmul ofGaussian)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalReciprocal (power)
open GaussianRationalL1 (qL1)
open GaussianCoefficientL1 (qL1_congr)
open GaussianRationalSyntheticBounds (natCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction)
open GaussianGammaCanonicalExponent (source)
open GaussianGammaC9Bound (majorant)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator independentRate)
open GaussianNameEquivalence (crossEquivalent)
open RationalArgmin (rationalLE)
open RationalArithmetic (multiply)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mixedNumerator (p q R d : PTm n) : PTm n := GaussianGammaOriginalPrefixRegularity.modulus R d*unit q+
  GaussianGammaCanonicalPrefixName.modulus R d*unit p
@[simp] theorem subst_mixedNumerator {l : ℕ} (σ : Fin n → PTm l) (p q R d : PTm n) :
    Syn.subst σ (mixedNumerator p q R d) = mixedNumerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ d) := by
  simp [mixedNumerator]

theorem term_error (p q z R B d e : PTm n) (h : Γ ⊢[PRAAx] source z R B) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (GaussianGammaOriginalPrefixRegularity.sourceTerm p z R B d e)
      (GaussianGammaCanonicalPrefixName.term q (ofGaussian z B) e)))
      (fraction (GaussianGammaCanonicalPrefixName.termModulus R d*(cap R d*unit q+unit p)) (radiusDenominator p q)) := by
  have pNorm : Γ ⊢[PRAAx] rationalLE (qL1 (power (ofGaussian z B) e)) (natCode (two*pw R d)) :=
    GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (le_refl one)
      (GaussianGammaOriginalPrefixRegularity.query_power_bound z R B d e h he)
  have cNorm := GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (denominator_positive (Γ := Γ) p q)
    (GaussianGammaOriginalPrefixCoefficientNames.original_reader_to_canonical p q R d e h.andE₁ he)
  have bound := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply (Γ := Γ) _ _)
    (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (GaussianRationalL1.qL1_nonnegative _)
      (GaussianRationalSyntheticBounds.natCode_nonnegative _) pNorm cNorm)
  have oldCode : Γ ⊢[PRAAx] GaussianGammaOriginalPrefixRegularity.sourceTerm p z R B d e ≐
      qmul (reader p R d e) (power (ofGaussian z B) e) :=
    GaussianGammaOriginalPrefixRegularity.term_as_reader _ _ _ _ _ _ he
  have code : Γ ⊢[PRAAx] qsub (GaussianGammaOriginalPrefixRegularity.sourceTerm p z R B d e)
      (GaussianGammaCanonicalPrefixName.term q (ofGaussian z B) e) ≐ qmul (power (ofGaussian z B) e)
      (qsub (reader p R d e) (GaussianGammaHigherCoefficientName.sample q e)) :=
    (qsub_congr oldCode (.eqRefl _)).eqTrans
      ((qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
        (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _))
  have scale : Γ ⊢[PRAAx] multiply (natCode (two*pw R d)) (fraction (two*(cap R d*unit q+unit p)) (radiusDenominator p q)) ≐
      fraction (GaussianGammaCanonicalPrefixName.termModulus R d*(cap R d*unit q+unit p)) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by unfold GaussianGammaCanonicalPrefixName.termModulus; ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr (qL1_congr code).eqSymm scale bound

theorem sum_error (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub
      (GaussianRationalFiniteSum.sum GaussianRationalPowerExpansion.termBody (succ d) (GaussianGammaOriginalPrefixRegularity.termData p z R B d))
      (GaussianGammaCanonicalPrefixName.rawValue q d (ofGaussian z B)))) (fraction (mixedNumerator p q R d) (radiusDenominator p q)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] GaussianFiniteSumL1Variation.termsError GaussianRationalPowerExpansion.termBody GaussianGammaCanonicalPrefixName.termBody
      (succ d) (GaussianGammaOriginalPrefixRegularity.termData p z R B d) (GaussianGammaCanonicalPrefixName.termData q (ofGaussian z B))
      (fraction (GaussianGammaCanonicalPrefixName.termModulus R d*(cap R d*unit q+unit p)) (radiusDenominator p q)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift d)) :: Γ.map Fm.shift
    have actual := RationalArgmin.rationalLE_congr (qL1_congr (qsub_congr
      (GaussianGammaOriginalPrefixRegularity.source_term_at (Γ := Δ) (Syn.shift p) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift d) (var 0))
      (GaussianGammaCanonicalPrefixName.term_at (Syn.shift q) (ofGaussian (Syn.shift z) (Syn.shift B)) (var 0)))).eqSymm (.eqRefl _)
      (term_error (Syn.shift p) (Syn.shift q) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift d) (var 0) hs.wk
        ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0))
    simpa only [Δ,Syn.shift,GaussianGammaOriginalPrefixRegularity.subst_termData,GaussianGammaCanonicalPrefixName.subst_termData,
      GaussianRationalHorner.subst_ofGaussian,GaussianGammaCanonicalPrefixName.subst_termModulus,
      GaussianGammaOriginalPrefixCoefficientVariation.subst_cap,GaussianCoefficientNameBounds.subst_unit,
      GaussianGammaInputPrecisionNorm.subst_radiusDenominator,GaussianEuclideanDistanceName.subst_fraction,
      PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_succ] using actual
  have scale : Γ ⊢[PRAAx] multiply (natCode (succ d))
      (fraction (GaussianGammaCanonicalPrefixName.termModulus R d*(cap R d*unit q+unit p)) (radiusDenominator p q)) ≐
      fraction (mixedNumerator p q R d) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by
        unfold mixedNumerator GaussianGammaOriginalPrefixRegularity.modulus GaussianGammaOriginalPrefixRegularity.termModulus
          GaussianGammaCanonicalPrefixName.modulus GaussianGammaCanonicalPrefixName.termModulus
        ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) scale (GaussianFiniteSumL1Variation.sum_error _ _ _ _ _ _ terms)

theorem raw_prefix_error (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (prefixValue p z R B d) (GaussianGammaCanonicalPrefixName.rawValue q d (ofGaussian z B))
      (mixedNumerator p q R d) (radiusDenominator p q) :=
  GaussianRationalReciprocal.bound_congr (qsub_congr (GaussianGammaOriginalPrefixRegularity.original_sum_binding p z R B d) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (denominator_positive p q) (sum_error p q z R B d h))

theorem named_observation_overlap (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaOriginalPrefixName.sample p z R B d)
      (GaussianGammaCanonicalPrefixName.sample q d R (ofGaussian z B)) (unit p+unit q) (unit p*unit q) := by
  let a := GaussianGammaOriginalPrefixName.clock p R d
  let b := GaussianGammaCanonicalPrefixName.clock q R d
  have left : Γ ⊢[PRAAx] le (GaussianGammaOriginalPrefixRegularity.modulus R d*unit p) (unit a) := GaussianFastValueCut.query_budget _ _
  have right : Γ ⊢[PRAAx] le (GaussianGammaCanonicalPrefixName.modulus R d*unit q) (unit b) := GaussianFastValueCut.query_budget _ _
  have rad : Γ ⊢[PRAAx] le (mixedNumerator a b R d*(unit p*unit q)) ((unit p+unit q)*(unit a*unit b)) :=
    le_congr (by unfold mixedNumerator; ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right (unit b*unit q) left) (mul_le_mul_right (unit a*unit p) right))
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive a b)
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive q)) rad
    (distance_congr (GaussianGammaOriginalPrefixName.sample_at p z R B d).eqSymm
      (GaussianGammaCanonicalPrefixName.sample_at q d R (ofGaussian z B)).eqSymm (.eqRefl _) (.eqRefl _)
      (raw_prefix_error a b z R B d h))

theorem original_prefix_is_canonical (z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaOriginalPrefixName.nameF GaussianGammaCanonicalPrefixName.nameF
      (GaussianGammaOriginalPrefixName.data z R B d) (GaussianGammaCanonicalPrefixName.data d R (ofGaussian z B)) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianGammaOriginalPrefixName.sample,GaussianGammaCanonicalPrefixName.sample,
    GaussianGammaOriginalPrefixName.subst_data,GaussianGammaCanonicalPrefixName.subst_data,GaussianRationalHorner.subst_ofGaussian,
    Syn.shift,unit,GaussianEuclideanPointDistance.unit] using named_observation_overlap (var 1) (var 0)
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift d)) hs

theorem original_rate (z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    independentRate GaussianGammaC7Name.nameF GaussianGammaOriginalPrefixName.nameF
      (GaussianGammaC7Name.data z R B) (GaussianGammaOriginalPrefixName.data z R B d)
      (majorant (two*R)) (GaussianGammaOriginalC19Prefix.denominator d) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate,GaussianGammaC7Name.sample,GaussianGammaOriginalPrefixName.sample,Syn.shift,GaussianGammaOriginalC19Prefix.denominator] using
    GaussianGammaOriginalPrefixName.original_named_C19_bound (var 1) (var 0)
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift d)) hs

theorem original_canonical_C19_bound (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (GaussianGammaCanonicalPrefixName.sample q d R (ofGaussian z B))
      (rateNumerator (majorant (two*R)) (GaussianGammaOriginalC19Prefix.denominator d) p q)
      (rateDenominator (GaussianGammaOriginalC19Prefix.denominator d) p q) :=
  GaussianNamedRateTransport.observation_error _ _ _ _ _ _ _ _ _ _ p q (unit_positive (succ d)) (original_rate z R B d h)
    (GaussianNameEquivalence.cross_refl _ _ (GaussianGammaC7Name.name_regular z R B h))
    (GaussianNameEquivalence.cross_symm _ _ _ _ (original_prefix_is_canonical z R B d h))

theorem original_Gamma_canonical_coefficient_prefix_identification_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent GaussianGammaOriginalPrefixName.nameF GaussianGammaCanonicalPrefixName.nameF
      (GaussianGammaOriginalPrefixName.data (var 0) (var 1) (var 2) (var 3))
      (GaussianGammaCanonicalPrefixName.data (var 3) (var 1) (ofGaussian (var 0) (var 2)))) :=
  closeUniv 4 (.impI (original_prefix_is_canonical _ _ _ _ Prf.hyp0))
theorem original_Gamma_canonical_coefficient_entire_series_C19_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) ⟶ distanceBounded (GaussianGammaC7Name.sample (var 0) (var 2) (var 3) (var 4))
      (GaussianGammaCanonicalPrefixName.sample (var 1) (var 5) (var 3) (ofGaussian (var 2) (var 4)))
      (rateNumerator (majorant (two*var 3)) (GaussianGammaOriginalC19Prefix.denominator (var 5)) (var 0) (var 1))
      (rateDenominator (GaussianGammaOriginalC19Prefix.denominator (var 5)) (var 0) (var 1))) :=
  closeUniv 6 (.impI (original_canonical_C19_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaPrefixCompatibility
