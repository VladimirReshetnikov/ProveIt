import IPRADerivations.Analysis.Gamma.EulerProducts.OriginalPrefixes.GaussianGammaOriginalPrefixCoefficientVariation
import IPRADerivations.Analysis.Gamma.Taylor.NamedCoefficients.GaussianGammaCoefficientRadiusIndependence

/-!
# Original cofinal prefix coefficients are the canonical coefficient names

The actual original whole-polynomial reader at precision p is compared
to the SAME canonical HigherCoefficientName at independent precision q.
The finite common cap supplies cap*2^(-p)+2^(-q), with no extra error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaOriginalPrefixCoefficientNames

open_ipra
open GaussianGammaOriginalC19Prefix (buffer totalDegree)
open GaussianGammaOriginalPrefixCoefficientVariation (cap precision)
open GaussianGammaFixedCoefficientVariation (modulus)
open GaussianGammaInputPrecisionNorm (radiusNumerator radiusDenominator denominator_positive)
open GaussianGammaFiniteCoefficientStability (fixedCoefficient)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def reader (p R d e : PTm n) : PTm n := exponentCoefficient (buffer p R d) (totalDegree p R d) e
def radiusPrecision (t R e : PTm n) : PTm n := precision (GaussianGammaRadiusCoefficientName.clock t (two*R) e) R e
ipra_subst reader [buffer, totalDegree, GaussianGammaOriginalC19Prefix.stage, GaussianGammaCofinalCoefficientName.coefficientPrecision, GaussianGammaCofinalCoefficientName.degreeCutoff, GaussianGammaCofinalCoefficientName.exponentialCutoff, GaussianGammaCofinalCoefficientName.exponentClock, GaussianGammaCofinalCoefficientName.inputClock, GaussianGammaCofinalCoefficientName.outerClock]
ipra_subst radiusPrecision

theorem reader_fixed (p R d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    reader p R d e ≐ fixedCoefficient (precision p R d) (two*R) e :=
  GaussianGammaOriginalPrefixCoefficientVariation.original_reader _ _ _ _ he
theorem radius_sample_fixed (t R e : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaRadiusCoefficientName.sample t (two*R) e ≐ fixedCoefficient (radiusPrecision t R e) (two*R) e :=
  (GaussianGammaRadiusCoefficientName.sample_at _ _ _).eqTrans
    (GaussianGammaOriginalPrefixCoefficientVariation.original_reader _ _ _ _ (le_refl e))
theorem radius_precision_later (t R e : PTm n) : Γ ⊢[PRAAx] le t (radiusPrecision t R e) :=
  le_trans (le_add_right t (GaussianFastValueCut.normalizer (modulus (two*R) e)))
    (GaussianGammaOriginalPrefixCoefficientVariation.precision_later _ _ _)

theorem reader_to_radius (p t R d e : PTm n) (hR : Γ ⊢[PRAAx] le one R) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    distanceBounded (reader p R d e) (GaussianGammaRadiusCoefficientName.sample t (two*R) e)
      (cap R d*radiusNumerator p t) (radiusDenominator p t) := by
  have old := distance_congr (Γ := Γ) (reader_fixed p R d e he).eqSymm (radius_sample_fixed t R e).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGammaAllDegreeCoefficientVariation.later_distance p t (precision p R d) (radiusPrecision t R e) (two*R) e
      (GaussianGammaOriginalPrefixCoefficientVariation.precision_later p R d) (radius_precision_later t R e)
      (GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R hR))
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive p t) (denominator_positive p t)
    (le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (radiusNumerator p t*radiusDenominator p t)
        (GaussianGammaOriginalPrefixCoefficientVariation.cap_bound R d e he))) old

theorem comparison_slack (p q t R d e : PTm n) (hR : Γ ⊢[PRAAx] le one R) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (reader p R d e) (GaussianGammaHigherCoefficientName.sample q e))
      (cap R d*unit q+unit p) (unit p*unit q) (cap R d+one) t := by
  have second := distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (mul_comm (unit t) (unit q))
    (GaussianNameEquivalence.cross_at _ _ _ _ t q
      (GaussianGammaCoefficientRadiusIndependence.original_canonical_identity (two*R) e
        (GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R hR)))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold radiusNumerator unit; ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_common_factor _ _ _ _ (unit p) _ (unit q) (unit t)
      (unit_positive p) (unit_positive q) (unit_positive t) (reader_to_radius p t R d e hR he) second)

theorem original_reader_to_canonical (p q R d e : PTm n) (hR : Γ ⊢[PRAAx] le one R) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    distanceBounded (reader p R d e) (GaussianGammaHigherCoefficientName.sample q e)
      (cap R d*unit q+unit p) (unit p*unit q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (cap R d+one) (positive_product _ _ (unit_positive p) (unit_positive q))
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI ?_
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,subst_reader,
    GaussianGammaHigherCoefficientName.subst_sample,GaussianGammaOriginalPrefixCoefficientVariation.subst_cap,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero,Syn.shift] using comparison_slack
      (Syn.shift p) (Syn.shift q) (var 0) (Syn.shift R) (Syn.shift d) (Syn.shift e) rs es

theorem original_actual_prefix_coefficients_are_canonical_Gamma_names_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ le (var 4) (var 3) ⟶ distanceBounded
      (reader (var 0) (var 2) (var 3) (var 4)) (GaussianGammaHigherCoefficientName.sample (var 1) (var 4))
        (cap (var 2) (var 3)*unit (var 1)+unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (.impI (original_reader_to_canonical _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaOriginalPrefixCoefficientNames
