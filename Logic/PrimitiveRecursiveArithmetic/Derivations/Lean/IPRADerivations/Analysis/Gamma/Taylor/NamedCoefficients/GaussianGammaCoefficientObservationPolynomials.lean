import IPRADerivations.Analysis.Gamma.Taylor.CoefficientEstimates.GaussianGammaAllDegreeCoefficientVariation
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaRadiusOverlap

/-!
# The original whole polynomials observed by the actual coefficient names

The SAME common-radius coefficient-name samples are literal coefficients
of these original full polynomials. Their unchanged whole evaluators are
the original cofinal C7 observations, so distinct radii have the exact
two-precision value comparison on their common original rational disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCoefficientObservationPolynomials

open_ipra
open GaussianRationalHorner (evaluate ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianGammaCanonicalExponent (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stage (p R e : PTm n) : PTm n := GaussianGammaRadiusCoefficientName.clock p R e+e
def precision (p R e : PTm n) : PTm n := GaussianGammaCofinalCoefficientName.coefficientPrecision (stage p R e) R
def degreeHorizon (p R e : PTm n) : PTm n := GaussianGammaCofinalCoefficientName.degreeCutoff (stage p R e) R
def exponentialHorizon (p R e : PTm n) : PTm n := GaussianGammaCofinalCoefficientName.exponentialCutoff (stage p R e) R
def degree (p R e : PTm n) : PTm n := GaussianGammaFiniteCoefficientPolynomial.totalDegree R (degreeHorizon p R e) (exponentialHorizon p R e)
def polynomial (p R e : PTm n) : PTm n := GaussianGammaFiniteCoefficientPolynomial.polynomial (precision p R e) R
  (degreeHorizon p R e) (exponentialHorizon p R e)
ipra_subst stage
ipra_subst precision [GaussianGammaCofinalCoefficientName.coefficientPrecision, GaussianGammaCofinalCoefficientName.exponentClock, GaussianGammaCofinalCoefficientName.inputClock, GaussianGammaCofinalCoefficientName.outerClock]
ipra_subst degreeHorizon [GaussianGammaCofinalCoefficientName.degreeCutoff, GaussianGammaCofinalCoefficientName.exponentClock, GaussianGammaCofinalCoefficientName.inputClock, GaussianGammaCofinalCoefficientName.outerClock]
ipra_subst exponentialHorizon [GaussianGammaCofinalCoefficientName.exponentialCutoff, GaussianGammaCofinalCoefficientName.outerClock]
ipra_subst degree
ipra_subst polynomial

theorem polynomial_length (p R e : PTm n) : Γ ⊢[PRAAx] length (polynomial p R e) ≐ succ (degree p R e) :=
  GaussianGammaFiniteCoefficientPolynomial.polynomial_length _ _ _ _
theorem stage_later (p R e : PTm n) : Γ ⊢[PRAAx] le p (stage p R e) :=
  le_trans (le_add_right p (GaussianFastValueCut.normalizer (GaussianGammaFixedCoefficientVariation.modulus R e)))
    (le_add_right (GaussianGammaRadiusCoefficientName.clock p R e) e)
theorem original_degree_guard (p R e : PTm n) : Γ ⊢[PRAAx] le e (degree p R e) := by
  have later : Γ ⊢[PRAAx] le e (exponentialHorizon p R e) :=
    le_trans (le_add_left e (GaussianGammaRadiusCoefficientName.clock p R e))
      (GaussianGammaCofinalCoefficientName.exponential_cutoff_cofinal (stage p R e) R)
  have positiveDegree : Γ ⊢[PRAAx] le one (GaussianGammaReciprocalDegreeCells.degree (degreeHorizon p R e)) :=
    le_of_eq_add (d := succ (degreeHorizon p R e)) (by unfold GaussianGammaReciprocalDegreeCells.degree; ipra_ring)
  have product : Γ ⊢[PRAAx] le (exponentialHorizon p R e)
      (exponentialHorizon p R e*GaussianGammaReciprocalDegreeCells.degree (degreeHorizon p R e)) :=
    le_congr (show Γ ⊢[PRAAx] exponentialHorizon p R e*one ≐ exponentialHorizon p R e by ipra_ring) (.eqRefl _)
      (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (exponentialHorizon p R e)) positiveDegree)
  exact le_trans (le_trans later product) (le_add_left _ _)

theorem original_coefficient_binding (p R e : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaRadiusCoefficientName.sample p R e ≐ entry (polynomial p R e) (monus (degree p R e) e) :=
  (GaussianGammaRadiusCoefficientName.sample_at p R e).eqTrans
    (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _ (original_degree_guard p R e))

theorem original_value_binding (p R e z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (polynomial p R e) (ofGaussian z B) ≐ GaussianGammaCofinalCoefficientName.sample (stage p R e) z R B :=
  GaussianGammaCofinalCoefficientName.actual_polynomial_observation _ _ _ _ hB

theorem cofinal_overlap (z R S B : PTm n) (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaCofinalCoefficientName.nameF GaussianGammaCofinalCoefficientName.nameF
      (GaussianGammaCofinalCoefficientName.data z R B) (GaussianGammaCofinalCoefficientName.data z S B) :=
  cross_trans _ _ _ _ _ _
    (cross_trans _ _ _ _ _ _ (GaussianGammaCofinalCoefficientName.original_C7_identity z R B hR)
      (GaussianGammaRadiusOverlap.original_P_overlap z R S B hR hS))
    (cross_symm _ _ _ _ (GaussianGammaCofinalCoefficientName.original_C7_identity z S B hS))

theorem original_value_overlap (p q R S e z B : PTm n)
    (hR : Γ ⊢[PRAAx] source z R B) (hS : Γ ⊢[PRAAx] source z S B) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (polynomial p R e) (ofGaussian z B)) (evaluate (polynomial q S e) (ofGaussian z B))
      (unit p+unit q) (unit p*unit q) := by
  have old := distance_congr (Γ := Γ) (original_value_binding p R e z B hR.andE₂.andE₁).eqSymm
    (original_value_binding q S e z B hS.andE₂.andE₁).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianNameEquivalence.cross_at _ _ _ _ (stage p R e) (stage q S e) (cofinal_overlap z R S B hR hS))
  have sa : Γ ⊢[PRAAx] le (unit p) (unit (stage p R e)) :=
    GaussianFactorBudget.power_monotone_length two p (stage p R e) (le_succ_self one) (stage_later p R e)
  have tb : Γ ⊢[PRAAx] le (unit q) (unit (stage q S e)) :=
    GaussianFactorBudget.power_monotone_length two q (stage q S e) (le_succ_self one) (stage_later q S e)
  have budget : Γ ⊢[PRAAx] le ((unit (stage p R e)+unit (stage q S e))*(unit p*unit q))
      ((unit p+unit q)*(unit (stage p R e)*unit (stage q S e))) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right (unit (stage p R e)*unit p) tb)
        (mul_le_mul_right (unit (stage q S e)*unit q) sa))
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive _) (unit_positive _))
    (GaussianRationalHorner.positive_product _ _ (unit_positive _) (unit_positive _)) budget old

theorem actual_original_coefficient_sample_polynomial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaRadiusCoefficientName.sample (var 0) (var 1) (var 2) ≐
      entry (polynomial (var 0) (var 1) (var 2)) (monus (degree (var 0) (var 1) (var 2)) (var 2))) :=
  closeUniv 3 (original_coefficient_binding _ _ _)
theorem actual_original_observation_polynomial_radius_overlap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 5) (var 2) (var 6) ⟶ source (var 5) (var 3) (var 6) ⟶
      distanceBounded (evaluate (polynomial (var 0) (var 2) (var 4)) (ofGaussian (var 5) (var 6)))
        (evaluate (polynomial (var 1) (var 3) (var 4)) (ofGaussian (var 5) (var 6)))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 7 (.impI (.impI (original_value_overlap _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaCoefficientObservationPolynomials
