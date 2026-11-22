import IPRADerivations.Analysis.GaussianGammaEulerHeadQuadratic
import IPRADerivations.Analysis.GaussianPolynomialExponentialLinear

/-!
# The actual second Gamma coefficient is the original Euler constant

The SAME finite coefficient polynomial has constant zero, linear one,
and quadratic coefficient equal to its actual sampled gamma code.
The original Euler-head harmonic contribution cancels the unchanged
sampled gamma-H_N input coefficient after actual convolution. Thus
the true cofinal family of stored second coefficients is a regular
Gaussian name cross-equivalent to the original canonical gamma name.
All coefficients are read from original buffers and all indices remain
internal. Coherence of arbitrary higher coefficients remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPolynomialQuadratic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul qadd canonical)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr)
open GaussianGammaPolynomialConstantLinear (input_constant input_linear exponential_constant head_low)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaLinearCoefficient (coefficient)
open GaussianGammaCanonicalExponent (harmonicPoint)
open GaussianGammaFiniteCoefficientPolynomial (polynomial totalDegree)
open GaussianGammaCofinalCoefficientName (coefficientPrecision degreeCutoff exponentialCutoff)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open RationalGaussianEmbedding (embed)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exponential_linear (q N L K : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    entry (GaussianRationalPolynomialExponential.polynomial (GaussianGammaExponentCoefficientPolynomial.polynomial q N L) (degree L) K)
      (monus (K*degree L) one) ≐ coefficient q N := by
  have input := input_linear (Γ := Γ) q N L
  have hc := GaussianRationalHorner.canonical_congr input (GaussianRationalMetric.qsub_canonical _ _)
  exact (GaussianPolynomialExponentialLinear.linear_value _ _ _ (input_constant q N L)
    (le_trans (le_succ_self one) (GaussianGammaZetaDegreeName.degree_positive L)) hK hc).eqTrans input

theorem whole_quadratic (q R L K : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    entry (polynomial q R L K) (monus (totalDegree R L K) two) ≐
      embed (GammaEulerConstantName.gammaSample q zero) := by
  have hN := GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive (Γ := Γ) R hR
  have headDegree : Γ ⊢[PRAAx] le two (succ (two*R)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right one hN)
  have expDegree : Γ ⊢[PRAAx] le two (K*degree L) :=
    le_congr (by ipra_ring) (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hK
      (GaussianGammaZetaDegreeName.degree_positive L))
  have low := GaussianPolynomialFirstCoefficients.quadratic_value (Γ := Γ)
    (GaussianGammaEulerHeadPolynomial.polynomial (two*R))
    (GaussianRationalPolynomialExponential.polynomial (GaussianGammaExponentCoefficientPolynomial.polynomial q (two*R) L) (degree L) K)
    (succ (two*R)) (K*degree L) headDegree expDegree
  have first := (qmul_congr (head_low (Γ := Γ) (two*R)).andE₁ (.eqRefl
    (entry (GaussianRationalPolynomialExponential.polynomial (GaussianGammaExponentCoefficientPolynomial.polynomial q (two*R) L) (degree L) K)
      (monus (K*degree L) two)))).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)
  have middle := (qmul_congr (head_low (Γ := Γ) (two*R)).andE₂ (exponential_linear q (two*R) L K hK)).eqTrans
    (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (GaussianRationalMetric.qsub_canonical _ _))
  have last := (qmul_congr (GaussianGammaEulerHeadQuadratic.head_quadratic (two*R) hN)
    (exponential_constant _ _ K (input_constant q (two*R) L))).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (RationalGaussianEmbedding.embed_canonical _))
  exact low.eqTrans ((qadd_congr (qadd_congr first middle) last).eqTrans
    ((qadd_congr (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qsub_canonical _ _)) (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans
        (GaussianRationalLinearProduct.add_sub_right _ _ (RationalGaussianEmbedding.embed_canonical _)))))

def secondObservation (p R : PTm n) : PTm n := entry
  (polynomial (coefficientPrecision (succ p) R) R (degreeCutoff (succ p) R) (exponentialCutoff (succ p) R))
  (monus (totalDegree R (degreeCutoff (succ p) R) (exponentialCutoff (succ p) R)) two)
@[simp] theorem subst_secondObservation {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (secondObservation p R) = secondObservation (Syn.subst σ p) (Syn.subst σ R) := by
  simp [secondObservation,coefficientPrecision,degreeCutoff,exponentialCutoff,
    GaussianGammaCofinalCoefficientName.exponentClock,GaussianGammaCofinalCoefficientName.inputClock,
    GaussianGammaCofinalCoefficientName.outerClock]
def nameF : PR 2 := PTm.toPR (secondObservation (var 0) (var 1))

theorem observation_at (p R : PTm n) : Γ ⊢[PRAAx] ap2 nameF p R ≐ secondObservation p R := by
  simpa only [nameF,ap2,subst_secondObservation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (secondObservation (var 0) (var 1) : PTm 2) ![p,R]

theorem second_observation_gamma (p R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    secondObservation p R ≐ embed (GammaEulerConstantName.gammaSample (coefficientPrecision (succ p) R) zero) :=
  whole_quadratic _ _ _ _ hR (le_trans (zero_lt_succ p) (GaussianGammaCofinalCoefficientName.exponential_cutoff_cofinal (succ p) R))

theorem coefficient_clock_later (p R : PTm n) : Γ ⊢[PRAAx] le p (coefficientPrecision (succ p) R) :=
  le_trans (le_succ_self p) (GaussianGammaCofinalCoefficientName.coefficient_precision_cofinal (succ p) R)

theorem independent_coefficient_error (p q R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p R) (ap2 GaussianGammaCanonicalExponent.gammaF q zero)
      (unit p+unit q) (unit p*unit q) :=
  distance_congr ((observation_at p R).eqTrans (second_observation_gamma p R hR)).eqSymm
    (GaussianGammaCanonicalExponent.gamma_sample_at q).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianGammaSynchronousExponentName.gamma_later_distance _ _ _ _ (coefficient_clock_later p R) (le_refl q))

theorem coefficient_regularity (p q R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p R) (ap2 nameF q R) (unit p+unit q) (unit p*unit q) :=
  distance_congr ((observation_at p R).eqTrans (second_observation_gamma p R hR)).eqSymm
    ((observation_at q R).eqTrans (second_observation_gamma q R hR)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianGammaSynchronousExponentName.gamma_later_distance _ _ _ _ (coefficient_clock_later p R) (coefficient_clock_later q R))

theorem name_regular (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx] pointCN nameF R := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift R)) := by
    simpa [Fm.shift,Syn.shift] using hR.shift.shift
  simpa only [pointCN,Syn.shift,unit,GaussianEuclideanPointDistance.unit] using coefficient_regularity (var 1) (var 0) _ hs

theorem original_gamma_identity (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianGammaCanonicalExponent.gammaF R zero := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift R)) := by
    simpa [Fm.shift,Syn.shift] using hR.shift.shift
  simpa only [crossEquivalent,Syn.shift,PTm.subst_zero] using independent_coefficient_error (var 1) (var 0) _ hs

theorem original_finite_Gamma_quadratic_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 3) ⟶ entry (polynomial (var 0) (var 1) (var 2) (var 3))
      (monus (totalDegree (var 1) (var 2) (var 3)) two) ≐ embed (GammaEulerConstantName.gammaSample (var 0) zero)) :=
  closeUniv 4 (.impI (.impI (whole_quadratic _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_cofinal_Gamma_second_coefficient_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ pointCN nameF (var 0) ⋏ crossEquivalent nameF GaussianGammaCanonicalExponent.gammaF (var 0) zero) :=
  closeUniv 1 (.impI (.andI (name_regular _ Prf.hyp0) (original_gamma_identity _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaPolynomialQuadratic
