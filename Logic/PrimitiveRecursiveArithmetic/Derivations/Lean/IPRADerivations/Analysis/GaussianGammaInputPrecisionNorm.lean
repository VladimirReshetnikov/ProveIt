import IPRADerivations.Analysis.GaussianCoefficientUniformNorm
import IPRADerivations.Analysis.GaussianGammaPowerHorizonCoherence
import IPRADerivations.Analysis.GaussianGammaWeierstrassFactors

/-!
# Precision variation of the original Gamma exponent coefficient buffer

The original gamma-H_N coefficient and every original signed reciprocal
power coefficient retain the original two-precision radius. Actual
reader and buffer lookup transport these estimates to all stored
entries. Genuine finite norm accumulation gives the numerical envelope
2(L+3)(2^-p+2^-q), uniformly in the unchanged harmonic cutoff N.
The original canonical C19 choice N=2(e+1), L=e is included explicitly.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaInputPrecisionNorm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul)
open GaussianRationalMetric (distanceBounded bounded qsub qnegative)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticBounds (natCode)
open GaussianGammaExponentCoefficientPolynomial (polynomial)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalPolynomialExponentialStability (exponent_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCoefficientL1 (coefficientNorm subCoefficients qL1_congr)
open GaussianRationalL1 (qL1)
open GaussianEuclideanDistanceName (fraction fraction_order)
open RationalGaussianEmbedding (embed)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radiusNumerator (p q : PTm n) : PTm n := unit p+unit q
def radiusDenominator (p q : PTm n) : PTm n := unit p*unit q
@[simp] theorem subst_radiusNumerator {m : ℕ} (σ : Fin n → PTm m) (p q : PTm n) :
    Syn.subst σ (radiusNumerator p q) = radiusNumerator (Syn.subst σ p) (Syn.subst σ q) := by simp [radiusNumerator]
@[simp] theorem subst_radiusDenominator {m : ℕ} (σ : Fin n → PTm m) (p q : PTm n) :
    Syn.subst σ (radiusDenominator p q) = radiusDenominator (Syn.subst σ p) (Syn.subst σ q) := by simp [radiusDenominator]
theorem denominator_positive (p q : PTm n) : Γ ⊢[PRAAx] le one (radiusDenominator p q) :=
  GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive q)

theorem original_linear_distance (p q N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaLinearCoefficient.coefficient p N) (GaussianGammaLinearCoefficient.coefficient q N)
      (radiusNumerator p q) (radiusDenominator p q) :=
  GaussianNameRingLaws.sum_left_error _ _ (qnegative (GaussianGammaCanonicalExponent.harmonicPoint N)) _ _
    (denominator_positive p q) (GaussianGammaSynchronousExponentName.gamma_later_distance p q p q (le_refl p) (le_refl q))

theorem original_weight_disk (j : PTm n) : Γ ⊢[PRAAx] bounded (GaussianFiniteLogarithmPolynomial.coefficient (succ j)) one one := by
  have norm : Γ ⊢[PRAAx] rationalLE (qL1 (GaussianFiniteLogarithmPolynomial.coefficient (succ j))) (fraction one one) :=
    RationalArgmin.rationalLE_congr (GaussianFiniteLogarithmWeightedNorm.coefficient_norm (succ j)).eqSymm (.eqRefl _)
      (fraction_order one (degree j) one one (zero_lt_succ _) (le_refl one)
        (le_congr (by ipra_ring) (by unfold degree; ipra_ring) (zero_lt_succ (succ j))))
  exact GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (le_refl one) norm

theorem original_high_distance (p q N j : PTm n) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (GaussianFiniteLogarithmPolynomial.coefficient (succ j)) (embed (RationalReciprocalPowerName.tailSample p (degree j) N)))
      (qmul (GaussianFiniteLogarithmPolynomial.coefficient (succ j)) (embed (RationalReciprocalPowerName.tailSample q (degree j) N)))
      (radiusNumerator p q) (radiusDenominator p q) := by
  have tail := RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (denominator_positive (Γ := Γ) p q)
    (RationalReciprocalPowerName.tail_samples_regularity p q (degree j) N (GaussianGammaZetaDegreeName.degree_positive j))
  exact distance_congr (.eqRefl _) (.eqRefl _) (one_mul _) (.eqRefl _)
    (GaussianGammaWeierstrassFactors.scaled_distance _ _ _ _ _ _ (denominator_positive p q) (original_weight_disk j) tail)

theorem zero_distance (p q : PTm n) : Γ ⊢[PRAAx] distanceBounded (qzero : PTm n) qzero (radiusNumerator p q) (radiusDenominator p q) :=
  GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ (denominator_positive p q) (denominator_positive p q)
    (le_congr (by ipra_ring) (.eqRefl _) (zero_le _))
    (GaussianRationalPowerDifference.distance_refl_zero qzero _ (denominator_positive p q))

theorem input_reader_distance (p q N L e : PTm n) (he : Γ ⊢[PRAAx] le e (degree L)) : Γ ⊢[PRAAx]
    distanceBounded (exponentCoefficient (polynomial p N L) (degree L) e)
      (exponentCoefficient (polynomial q N L) (degree L) e) (radiusNumerator p q) (radiusDenominator p q) := by
  refine .orE (zero_or_succ e) ?_ ?_
  · exact distance_congr
      ((exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (GaussianGammaExponentCoefficientStability.zero_reader p N L)).eqSymm
      ((exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (GaussianGammaExponentCoefficientStability.zero_reader q N L)).eqSymm
      (.eqRefl _) (.eqRefl _) (zero_distance p q)
  · refine .orE (zero_or_succ (pred e)) ?_ ?_
    · have form : ((pred e ≐ zero) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      exact distance_congr
        ((exponent_congr (.eqRefl _) (.eqRefl _) form).eqTrans (GaussianGammaExponentCoefficientStability.linear_reader p N L)).eqSymm
        ((exponent_congr (.eqRefl _) (.eqRefl _) form).eqTrans (GaussianGammaExponentCoefficientStability.linear_reader q N L)).eqSymm
        (.eqRefl _) (.eqRefl _) (original_linear_distance p q N)
    · have form : ((pred e ≐ succ (pred (pred e))) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ degree (pred (pred e)) :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have hl := le_congr form (.eqRefl _) he.wk.wk
      have hj : ((pred e ≐ succ (pred (pred e))) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] le (pred (pred e)) L :=
        (succ_monus_succ _ _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans hl)
      exact distance_congr
        ((exponent_congr (.eqRefl _) (.eqRefl _) form).eqTrans (GaussianGammaExponentCoefficientStability.high_reader p N L _ hj)).eqSymm
        ((exponent_congr (.eqRefl _) (.eqRefl _) form).eqTrans (GaussianGammaExponentCoefficientStability.high_reader q N L _ hj)).eqSymm
        (.eqRefl _) (.eqRefl _) (original_high_distance p q N _)

theorem input_entry_distance (p q N L i : PTm n) (hi : Γ ⊢[PRAAx] le i (degree L)) : Γ ⊢[PRAAx]
    distanceBounded (entry (polynomial p N L) i) (entry (polynomial q N L) i) (radiusNumerator p q) (radiusDenominator p q) := by
  have complement := GaussianRationalMonicReconstruction.complement (Γ := Γ) (degree L) i hi
  exact distance_congr
    ((exponent_inside _ _ _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans (entry_congr (.eqRefl _) complement))
    ((exponent_inside _ _ _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans (entry_congr (.eqRefl _) complement))
    (.eqRefl _) (.eqRefl _)
    (input_reader_distance p q N L (monus (degree L) i) (GaussianRationalMonicReconstruction.monus_le_left _ _))

theorem input_difference_entries (p q N L : PTm n) : Γ ⊢[PRAAx]
    GaussianCoefficientUniformNorm.entryBounds (subCoefficients (polynomial p N L) (polynomial q N L) (succ (degree L)))
      (succ (degree L)) (fraction (two*radiusNumerator p q) (radiusDenominator p q)) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (succ (degree L))) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] lt (var 0) (succ (degree (Syn.shift L))) := by
    simpa only [Δ,Syn.shift,PTm.subst_succ,GaussianGammaReciprocalDegreeCells.subst_degree] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have hi : Δ ⊢[PRAAx] le (var 0) (degree (Syn.shift L)) :=
    (succ_monus_succ (var 0) (degree (Syn.shift L))).eqSymm.eqTrans range
  have bounds : Δ ⊢[PRAAx] rationalLE (qL1 (qsub
      (entry (polynomial (Syn.shift p) (Syn.shift N) (Syn.shift L)) (var 0))
      (entry (polynomial (Syn.shift q) (Syn.shift N) (Syn.shift L)) (var 0))))
      (fraction (two*radiusNumerator (Syn.shift p) (Syn.shift q)) (radiusDenominator (Syn.shift p) (Syn.shift q))) :=
    GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (denominator_positive (Γ := Δ) (Syn.shift p) (Syn.shift q))
      (input_entry_distance (Syn.shift p) (Syn.shift q) (Syn.shift N) (Syn.shift L) (var 0) hi)
  have same := GaussianCoefficientL1.sub_lookup (Γ := Δ) (polynomial (Syn.shift p) (Syn.shift N) (Syn.shift L))
    (polynomial (Syn.shift q) (Syn.shift N) (Syn.shift L)) (succ (degree (Syn.shift L))) (var 0) ((succ_monus_succ _ _).eqTrans hi)
  simpa only [Δ,GaussianCoefficientUniformNorm.entryBounds,Syn.shift,GaussianCoefficientL1.subst_subCoefficients,
    GaussianGammaExponentCoefficientPolynomial.subst_polynomial,GaussianGammaReciprocalDegreeCells.subst_degree,
    PTm.subst_succ,GaussianEuclideanDistanceName.subst_fraction,PTm.subst_mul,PTm.subst_succ,PTm.subst_zero,
    subst_radiusNumerator,subst_radiusDenominator] using
      RationalArgmin.rationalLE_congr (qL1_congr same).eqSymm (.eqRefl _) bounds

theorem input_precision_norm (p q N L : PTm n) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (subCoefficients (polynomial p N L) (polynomial q N L) (succ (degree L))))
      (fraction (two*succ (degree L)*radiusNumerator p q) (radiusDenominator p q)) := by
  have actual := GaussianCoefficientUniformNorm.coefficient_uniform _ _ _
    (GaussianCoefficientL1.zip_length GaussianCoefficientL1.subF _ _ _) (input_difference_entries (Γ := Γ) p q N L)
  have code : Γ ⊢[PRAAx] RationalArithmetic.multiply (natCode (succ (degree L)))
      (fraction (two*radiusNumerator p q) (radiusDenominator p q)) ≐
        fraction (two*succ (degree L)*radiusNumerator p q) (radiusDenominator p q) :=
    (RationalNonnegativePowers.fraction_multiply (Γ := Γ) (succ (degree L)) one
    (two*radiusNumerator p q) (radiusDenominator p q) (le_refl one) (denominator_positive p q)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by ipra_ring) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) code actual

theorem original_Gamma_input_precision_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rationalLE (coefficientNorm (subCoefficients (polynomial (var 0) (var 2) (var 3)) (polynomial (var 1) (var 2) (var 3)) (succ (degree (var 3)))))
      (fraction (two*succ (degree (var 3))*radiusNumerator (var 0) (var 1)) (radiusDenominator (var 0) (var 1)))) :=
  closeUniv 4 (input_precision_norm _ _ _ _)
theorem original_C19_canonical_input_precision_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rationalLE (coefficientNorm (subCoefficients (polynomial (var 0) (two*succ (var 2)) (var 2))
      (polynomial (var 1) (two*succ (var 2)) (var 2)) (succ (degree (var 2)))))
      (fraction (two*succ (degree (var 2))*radiusNumerator (var 0) (var 1)) (radiusDenominator (var 0) (var 1)))) :=
  closeUniv 3 (input_precision_norm _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaInputPrecisionNorm
