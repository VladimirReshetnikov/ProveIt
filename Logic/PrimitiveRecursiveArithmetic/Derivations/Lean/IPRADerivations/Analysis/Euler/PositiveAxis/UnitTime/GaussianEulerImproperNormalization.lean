import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitIntegrand
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitEndpointDecay
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerImproperName
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayCompactAntiderivative
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianRobinMeshExponential

/-!
# Unit normalization of the original improper Euler integral

The same finite grid becomes the original decay quadrature when its
encoded argument is one. Its antiderivative is the actual difference
of two decay observations. The prescribed varying endpoints put the
finite result within nine dyadic errors of one. Removing that auxiliary
error gives independent observation equivalence and, at the canonical
unit argument, agreement with the original finite-product Gamma name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerImproperNormalization

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianEulerImproperName (data nameF source)
open GaussianEulerIntegrandName (coefficient fixedData)
open GaussianEulerDecayCompactAntiderivative (endpointF endpointData endpoint_at compact_observations mesh_covers_step)
open GaussianEulerUnitIntegrand (unit_coefficient exact_quadrature)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width width_bound)
open GaussianGammaEulerCompactQuadrature (localFactor)
open GaussianCompactRiemannName (mesh precision)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNamedInverseRate (rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem local_factor_positive (p A R : PTm n) : Γ ⊢[PRAAx] le one (localFactor p A R) := by
  unfold localFactor GaussianEulerCompactModulus.lipschitz
  apply positive_product
  · unfold GaussianRadiusExponentialLipschitzRate.factor
    exact GaussianFactorBudget.power_positive _ _
      (le_trans (le_succ_self one) (le_succ_self two))
  · unfold GaussianEulerExponentCompactBounds.factor
    exact le_add_left one _

theorem compact_decay_sample (p q z R B A : PTm n) (h : Γ ⊢[PRAAx] coefficient z B ≐ qzero) :
    Γ ⊢[PRAAx] ap2 GaussianGammaEulerCompactQuadrature.nameF q (GaussianGammaEulerCompactQuadrature.data z R B p A) ≐
      ap2 (GaussianCompactRiemannName.nameF GaussianEulerDecayQuadrature.evaluatorF) q
        (GaussianCompactRiemannName.data one (width p A R) (etaDen p A R) (localFactor p A R)
          (top p A R) (fixedData z B)) := by
  let C := width p A R
  let E := etaDen p A R
  let L := localFactor p A R
  let T := top p A R
  let X := fixedData z B
  let G := GaussianEulerDecayQuadrature.evaluatorF
  have decay : Γ ⊢[PRAAx] ap2 (GaussianCompactRiemannName.nameF G) q
      (GaussianCompactRiemannName.data one C E L T X) ≐
        GaussianCompactRiemannName.quadrature G (precision q T) (mesh q L T) one C E X :=
    GaussianCompactRiemannName.name_at G q one C E L T X
  exact (GaussianGammaEulerCompactQuadrature.original_sample q z R B p A).eqTrans
    ((exact_quadrature (precision q T) (mesh q L T) one C E z B h).eqTrans decay.eqSymm)

theorem diagonal_at_one (p z R B A : PTm n) (ha : Γ ⊢[PRAAx] le one A)
    (hcoef : Γ ⊢[PRAAx] coefficient z B ≐ qzero) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B A)) qone (num 9) (unit p) := by
  let C := width p A R
  let E := etaDen p A R
  let L := localFactor p A R
  let T := top p A R
  let Y := endpointData one C E
  let W := ap2 endpointF p Y
  let X := ap2 nameF p (data z R B A)
  let U := unit p
  let V := unit (p+num 4)
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hv : Γ ⊢[PRAAx] le one V := unit_positive _
  have compare : Γ ⊢[PRAAx] le ((V+U)*U) (two*(V*U)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (V*U) (mul_le_mul_right U (GaussianExponentialReference.unit_monotone (le_add_right p (num 4)))))
  have bound := compact_observations (Γ := Γ) (p+num 4) p one C E L T (fixedData z B) (le_refl _)
    (GaussianGammaCompactCutoffGeometry.width_positive p A R) (GaussianGammaIntegralCutoffs.eta_den_positive p A R)
    (local_factor_positive p A R) (width_bound p A R)
    (mesh_covers_step (p+num 4) C E L T (width_bound p A R) (local_factor_positive p A R))
  have equal : Γ ⊢[PRAAx] X ≐ ap2 (GaussianCompactRiemannName.nameF GaussianEulerDecayQuadrature.evaluatorF)
      (p+num 4) (GaussianCompactRiemannName.data one C E L T (fixedData z B)) :=
    (GaussianEulerImproperName.original_observation p z R B A).eqTrans
      (compact_decay_sample p (p+num 4) z R B A hcoef)
  have first : Γ ⊢[PRAAx] distanceBounded X W two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hv hu) hu compare
      (distance_congr equal.eqSymm (.eqRefl W) (.eqRefl _) (.eqRefl _) bound)
  have endpoints := GaussianEulerUnitEndpointDecay.cutoff_endpoint_difference p (p+one) A R ha (le_refl _)
  have hs := unit_positive (Γ := Γ) (p+one)
  have second : Γ ⊢[PRAAx] distanceBounded W qone (num 7) U :=
    distance_radius_mono _ _ _ _ _ _ hs hu
      (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (num 7))
        (GaussianExponentialReference.unit_monotone (le_add_right p one)))
      (distance_congr (endpoint_at p one C E).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) endpoints)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same X W qone two (num 7) U hu first second)

theorem original_unit_observations (p q z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hcoef : Γ ⊢[PRAAx] coefficient z B ≐ qzero) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B A)) (ap2 constantF q qone)
      (unit p+unit q) (unit p*unit q) := by
  let x := data z R B A
  have diagonal : Γ ⊢[PRAAx] diagonalEnvelope nameF constantF x qone zero one (num 9) := by
    have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift, Syn.shift] using h.andE₂.andE₁.shift
    have hc : Γ.map Fm.shift ⊢[PRAAx] coefficient (Syn.shift z) (Syn.shift B) ≐ qzero := by
      simpa [Fm.shift, Syn.shift] using hcoef.shift
    refine .allI ?_
    have atp := diagonal_at_one (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) hs hc
    simpa only [diagonalEnvelope, x, GaussianEulerImproperName.subst_data, Syn.shift,
      GaussianRationalSyntheticDivision.subst_qone, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] using
        distance_congr (.eqRefl _) (constant_at (var 0) qone).eqSymm
          (by unfold diagonalNumerator; simp only [LeanProofs.IPRA.PTm.subst_num]; ipra_ring)
          (by unfold diagonalDenominator; ipra_ring) atp
  have rate := GaussianNamedLipschitzRate.independent_at nameF constantF x qone zero one (num 9) p q (le_refl _)
    (GaussianEulerImproperName.name_regular z R B A h) (constant_regular _) diagonal
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) rate

theorem original_unit_normalization (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hcoef : Γ ⊢[PRAAx] coefficient z B ≐ qzero) :
    Γ ⊢[PRAAx] crossEquivalent nameF constantF (data z R B A) qone := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerImproperName.subst_source] using h.shift.shift
  have hc : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      coefficient (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B)) ≐ qzero := by
    simpa [Fm.shift,Syn.shift] using hcoef.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianEulerImproperName.subst_data,Syn.shift,
    GaussianRationalSyntheticDivision.subst_qone,GaussianEuclideanPointDistance.unit,unit] using
    original_unit_observations (var 1) (var 0) _ _ _ _ hs hc

theorem unit_source : Γ ⊢[PRAAx] source (oneCode : PTm n) one one one := by
  let h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source oneCode one one :=
    GaussianGammaNormalization.unit_source.andE₂
  refine .andI h (.andI (le_refl _) (.andI h ?_))
  unfold GaussianEulerLowerPowerCoefficients.realLower
  apply zle_of_toZ zero
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_one]
  ipra_simps
  ring

theorem improper_at_one : Γ ⊢[PRAAx] crossEquivalent nameF constantF (data (oneCode : PTm n) one one one) qone :=
  original_unit_normalization _ _ _ _ unit_source unit_coefficient

theorem agrees_with_Gamma_at_one : Γ ⊢[PRAAx] crossEquivalent nameF GaussianGammaReciprocalInverse.gammaF
    (data (oneCode : PTm n) one one one) (GaussianGammaReciprocalInverse.gammaData oneCode one one one) := by
  apply GaussianNameEquivalence.cross_trans nameF constantF GaussianGammaReciprocalInverse.gammaF _ qone _
    improper_at_one
  apply GaussianNameEquivalence.cross_symm
  exact GaussianNameEquivalence.cross_trans _ GaussianNameRingLaws.oneF constantF _ zero _
    (GaussianGammaNormalization.original_Gamma_one GaussianRobinMeshExponential.all_mesh_exponential_inverses)
    GaussianGammaEncodingRescaling.one_constant_cross

theorem original_Euler_improper_integral_is_one_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] crossEquivalent nameF constantF (data oneCode one one one) qone :=
  improper_at_one

theorem original_Euler_improper_integral_agrees_with_Gamma_at_one_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] crossEquivalent nameF GaussianGammaReciprocalInverse.gammaF
      (data oneCode one one one) (GaussianGammaReciprocalInverse.gammaData oneCode one one one) :=
  agrees_with_Gamma_at_one

end LeanProofs.IPRA.Analysis.GaussianEulerImproperNormalization
