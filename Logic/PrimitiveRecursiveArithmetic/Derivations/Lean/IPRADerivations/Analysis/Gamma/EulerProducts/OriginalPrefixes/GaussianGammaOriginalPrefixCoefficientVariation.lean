import IPRADerivations.Analysis.Gamma.EulerProducts.OriginalPrefixes.GaussianGammaOriginalC19Prefix
import IPRADerivations.Analysis.Gamma.Taylor.CoefficientEstimates.GaussianGammaAllDegreeCoefficientVariation
import IPRADerivations.Foundations.FiniteQueryDemand

/-!
# A computed common modulus for the original C19 prefix coefficients

All coefficients through the internal d are read from the SAME original
cofinal whole-polynomial observation. A genuine finite maximum of their
already proved original moduli bounds their precision variation uniformly.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaOriginalPrefixCoefficientVariation

open_ipra
open GaussianGammaOriginalC19Prefix (stage buffer totalDegree)
open GaussianGammaFixedCoefficientVariation (modulus)
open GaussianGammaInputPrecisionNorm (radiusNumerator radiusDenominator denominator_positive)
open GaussianGammaFiniteCoefficientStability (fixedCoefficient)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def modulusBody : PTm 2 := modulus (two*var 1) (var 0)
def cap (R d : PTm n) : PTm n := one+LeanProofs.IPRA.Foundations.FiniteQueryDemand.finiteMaximum modulusBody (succ d) R
def precision (q R d : PTm n) : PTm n := GaussianGammaCofinalCoefficientName.coefficientPrecision (stage q d) (two*R)
ipra_subst cap
ipra_subst precision [stage, GaussianGammaCofinalCoefficientName.coefficientPrecision, GaussianGammaCofinalCoefficientName.exponentClock, GaussianGammaCofinalCoefficientName.inputClock, GaussianGammaCofinalCoefficientName.outerClock]

theorem modulus_body_at (R e : PTm n) : Γ ⊢[PRAAx] inst2 modulusBody e R ≐ modulus (two*R) e := by
  simp only [modulusBody,inst2,GaussianGammaFixedCoefficientVariation.subst_modulus,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact .eqRefl _
theorem cap_positive (R d : PTm n) : Γ ⊢[PRAAx] le one (cap R d) := le_add_right _ _
theorem cap_bound (R d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx] le (modulus (two*R) e) (cap R d) := by
  have actual : Γ ⊢[PRAAx] le (inst2 modulusBody e R) (LeanProofs.IPRA.Foundations.FiniteQueryDemand.finiteMaximum modulusBody (succ d) R) :=
    LeanProofs.IPRA.Foundations.FiniteQueryDemand.finiteMaximum_at modulusBody ((succ_monus_succ _ _).eqTrans he)
  exact le_trans (le_congr (modulus_body_at R e) (.eqRefl _) actual) (le_add_left _ _)

theorem original_reader (q R d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    exponentCoefficient (buffer q R d) (totalDegree q R d) e ≐ fixedCoefficient (precision q R d) (two*R) e := by
  let L := GaussianGammaCofinalCoefficientName.degreeCutoff (stage q d) (two*R)
  let K := GaussianGammaCofinalCoefficientName.exponentialCutoff (stage q d) (two*R)
  have below : Γ ⊢[PRAAx] le e (stage q d) := le_trans he (le_add_left d q)
  have hL : Γ ⊢[PRAAx] le e (GaussianGammaReciprocalDegreeCells.degree L) :=
    le_trans (le_trans below (GaussianGammaCofinalCoefficientName.degree_cutoff_cofinal _ _))
      (le_of_eq_add (d := two) (by unfold GaussianGammaReciprocalDegreeCells.degree; ipra_ring))
  have hK : Γ ⊢[PRAAx] le e K := le_trans below (GaussianGammaCofinalCoefficientName.exponential_cutoff_cofinal _ _)
  exact GaussianGammaAllDegreeCoefficientStability.original_fixed_horizon (precision q R d) (two*R) L K e hL hK

theorem precision_later (q R d : PTm n) : Γ ⊢[PRAAx] le q (precision q R d) :=
  le_trans (le_add_right q d) (GaussianGammaCofinalCoefficientName.coefficient_precision_cofinal _ _)

theorem original_reader_distance (p q R d e : PTm n) (hR : Γ ⊢[PRAAx] le one R) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    distanceBounded (exponentCoefficient (buffer p R d) (totalDegree p R d) e)
      (exponentCoefficient (buffer q R d) (totalDegree q R d) e)
        (cap R d*radiusNumerator p q) (radiusDenominator p q) := by
  have old := distance_congr (Γ := Γ) (original_reader p R d e he).eqSymm (original_reader q R d e he).eqSymm
    (.eqRefl _) (.eqRefl _)
      (GaussianGammaAllDegreeCoefficientVariation.later_distance p q (precision p R d) (precision q R d) (two*R) e
        (precision_later p R d) (precision_later q R d) (GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R hR))
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive p q) (denominator_positive p q)
    (le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (radiusNumerator p q*radiusDenominator p q) (cap_bound R d e he))) old

theorem original_common_prefix_coefficient_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ le (var 4) (var 3) ⟶ distanceBounded
      (exponentCoefficient (buffer (var 0) (var 2) (var 3)) (totalDegree (var 0) (var 2) (var 3)) (var 4))
      (exponentCoefficient (buffer (var 1) (var 2) (var 3)) (totalDegree (var 1) (var 2) (var 3)) (var 4))
        (cap (var 2) (var 3)*radiusNumerator (var 0) (var 1)) (radiusDenominator (var 0) (var 1))) :=
  closeUniv 5 (.impI (.impI (original_reader_distance _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaOriginalPrefixCoefficientVariation
