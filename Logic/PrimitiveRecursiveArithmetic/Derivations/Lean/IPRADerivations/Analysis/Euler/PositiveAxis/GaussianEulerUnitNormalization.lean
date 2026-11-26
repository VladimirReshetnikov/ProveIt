import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitNormalizationCompact
import IPRADerivations.Analysis.Gamma.GaussianEulerIntegralGammaIdentification
import IPRADerivations.Core.CongruenceTactic

/-!
# Unit normalization derived from the original Euler integral

The original unit-input compact observations are the decay endpoint
difference. The original eta endpoint approaches one and the original
integer top endpoint approaches zero. Ordinary point CN and one finite
rational gap give the unit value of the unchanged improper name. Only
after that independent integral derivation is the Euler/Gamma identity
used to obtain the same original Gamma value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode)
open GaussianEulerIntegrandName (evaluatorF fixedData decayF decayData)
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianEulerCompactModulus (lipschitz)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent)
open GaussianGammaCanonicalExponent (constantF constant_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def integralData : PTm n := GaussianEulerImproperName.data oneCode one one one
def integral (p : PTm n) : PTm n := ap2 GaussianEulerImproperName.nameF p integralData
def compact (p k : PTm n) : PTm n := ap2 GaussianGammaEulerCompactQuadrature.nameF p
  (GaussianGammaEulerCompactQuadrature.data oneCode one one k one)
@[simp] theorem subst_integralData {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (integralData : PTm n) = (integralData : PTm m) := by simp [integralData]
@[simp] theorem subst_integral {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) : Syn.subst σ (integral p) = integral (Syn.subst σ p) := by simp [integral]

theorem unit_lower_source : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source (oneCode : PTm n) one one one := by
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (oneCode : PTm n) (one*one) :=
    le_congr ComplexLogarithmRemainder.normSq_one.eqSymm (by ipra_ring) (le_refl one)
  have margin : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower (oneCode : PTm n) one one := by
    unfold GaussianEulerLowerPowerCoefficients.realLower
    apply zle_of_toZ zero
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_one]
    try ipra_simps
    ring
  exact .andI (le_refl one) (.andI (.andI (le_refl one) disk) margin)

theorem integral_regular : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN GaussianEulerImproperName.nameF (integralData : PTm n) :=
  GaussianEulerImproperName.name_regular oneCode one one one (.andI unit_lower_source.andE₂.andE₁ unit_lower_source)

theorem lipschitz_positive (R E T : PTm n) : Γ ⊢[PRAAx] le one (lipschitz R E T) :=
  positive_product _ _ (GaussianPolynomialPerturbation.power_positive _ _ (le_of_eq_add (d := two) (by ipra_ring)))
    (le_add_left one ((R+one)*E))

theorem width_positive (k : PTm n) : Γ ⊢[PRAAx] le one (width k one one) := by
  have ht : Γ ⊢[PRAAx] le two (top k one one) := le_congr (by ipra_ring : Γ ⊢[PRAAx] two*one ≐ two) (.eqRefl _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl two) (GaussianGammaIntegralCutoffs.height_positive k one one))
  have he : Γ ⊢[PRAAx] le (top k one one) (etaDen k one one*top k one one) := le_congr (one_mul _) (.eqRefl _)
    (mul_le_mul_right (top k one one) (GaussianGammaIntegralCutoffs.eta_den_positive k one one))
  have htwo := le_trans ht he
  have split := natEq (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint (Γ := Γ) k one one)
  unfold width at split ⊢
  ipra_le sl htwo using linear_combination split

theorem compact_endpoint (p q k : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (compact p k)
      (qsub (ap2 decayF (q+one) (decayData one (etaDen k one one))) (ap2 decayF (q+one) (decayData (top k one one) one)))
      (unit p+unit q) (unit p*unit q) := by
  let E := etaDen k one one
  let C := width k one one
  let T := top k one one
  let L := lipschitz one E T
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k one one
  have actual := GaussianEulerUnitNormalizationCompact.original_compact_endpoint p q one C E L T zero
    (le_refl one) (width_positive k) hE (lipschitz_positive one E T) (GaussianGammaCompactQuadratureBoundary.width_bound k one one)
  have scale : Γ ⊢[PRAAx] GaussianEulerDecayMesh.observation (one+C) E (q+one) ≐
      GaussianEulerDecayMesh.observation (T*E) (one*E) (q+one) := by
    ipra_congr (GaussianEulerDecayMesh.observation (var 0) (var 1) (var 2) : PTm 3) with
      [(GaussianGammaCompactQuadratureBoundary.exact_right_endpoint k one one).eqTrans (mul_comm E T),
        (one_mul E).eqSymm, .eqRefl (q+one)]
  have right := scale.eqTrans (GaussianEulerDecayMesh.observation_rescale T one E (q+one) (le_refl one) hE)
  exact distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) right) (.eqRefl _) (.eqRefl _) actual

theorem cutoff_growth (k : PTm n) : Γ ⊢[PRAAx]
    le (unit k) (etaDen k one one) ⋏ le (unit k) (unit (top k one one)) := by
  have hk : Γ ⊢[PRAAx] le k (height k one one) := by unfold height; ipra_le 𝔞 one+𝔞 (GaussianGammaIntegralCutoffs.tailCoefficient one)+10
  have he := GaussianExponentialReference.unit_monotone hk
  have htop : Γ ⊢[PRAAx] le (height k one one) (top k one one) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (height k one one) (le_succ_self one))
  have eq : Γ ⊢[PRAAx] etaDen k one one ≐ unit (height k one one) := congrAp2 powF (one_mul _) (.eqRefl two)
  exact .andI (le_congr (.eqRefl _) eq.eqSymm he) (GaussianExponentialReference.unit_monotone (le_trans hk htop))

theorem endpoint_dyadic (p k : PTm n) (hpk : Γ ⊢[PRAAx] le k p) : Γ ⊢[PRAAx]
    distanceBounded (qsub (ap2 decayF p (decayData one (etaDen k one one))) (ap2 decayF p (decayData (top k one one) one))) qone
      (num 6) (unit k) := by
  let E := etaDen k one one
  let T := top k one one
  let P := unit p
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k one one
  have den := positive_product _ _ hE (positive_product _ _ (unit_positive T) (unit_positive p))
  have growth := cutoff_growth (Γ := Γ) k
  have precision := GaussianExponentialReference.unit_monotone hpk
  have first := mul_le_mul_right (num 3*unit T*P) growth.andE₁
  have second := mul_le_mul_right (E*P) growth.andE₂
  have third := mul_le_mul_right (two*E*unit T) precision
  have total := add_le_add₂ (add_le_add₂ first second) third
  exact distance_radius_mono _ _ _ _ _ _ den (unit_positive k)
    (le_congr (by ipra_ring) (by ipra_ring) total)
    (GaussianEulerUnitNormalizationCompact.original_endpoint_difference_near_one p E T hE)

theorem integral_dyadic (k : PTm n) : Γ ⊢[PRAAx] distanceBounded (integral k) qone (num 8) (unit k) := by
  let r := k+num 4
  have hk : Γ ⊢[PRAAx] le k r := le_add_right _ _
  have later := GaussianExponentialReference.unit_monotone hk
  have raw := compact_endpoint (Γ := Γ) r r k
  have first := distance_radius_mono _ _ _ _ two (unit k) (positive_product _ _ (unit_positive r) (unit_positive r)) (unit_positive k)
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (mul_le_mul_right (unit r) later) (mul_le_mul_right (unit r) later))) raw
  have joined := distance_triangle_same _ _ _ _ _ _ (unit_positive k) first (endpoint_dyadic (r+one) k (le_trans hk (le_add_right r one)))
  exact distance_congr (GaussianEulerImproperName.original_observation k oneCode one one one).eqSymm (.eqRefl _)
    (by ipra_ring) (.eqRefl _) joined

theorem integral_slack (p t : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (integral p) qone) one (unit p) (num 9) t := by
  have hp := unit_positive (Γ := Γ) p
  have ht := unit_positive (Γ := Γ) t
  have hd := positive_product _ _ hp ht
  have first := GaussianNameEquivalence.point_at (Γ := Γ) GaussianEulerImproperName.nameF integralData p t integral_regular
  have second := distance_radius_mono _ _ _ _ (num 8*unit p) (unit p*unit t) ht hd
    (le_of_eq_add (d := zero) (by ipra_ring)) (integral_dyadic t)
  have joined := distance_triangle_same _ _ _ _ _ _ hd first second
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by unfold unit; ipra_ring) (.eqRefl _) joined

theorem original_integral_one_observation (p : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (integral p) qone one (unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (num 9) (unit_positive p)
    (integral_slack p (GaussianRationalSlackRemoval.precision (qsub (integral p) qone) one (unit p) (num 9)))

theorem original_integral_one : Γ ⊢[PRAAx] crossEquivalent GaussianEulerImproperName.nameF constantF (integralData : PTm n) qone := by
  refine .allI (.allI ?_)
  have near := original_integral_one_observation (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1)
  have hu := positive_product (Γ := (Γ.map Fm.shift).map Fm.shift) _ _ (unit_positive (var 1)) (unit_positive (var 0))
  have larger := distance_radius_mono _ _ one (unit (var 1)) (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0)) (unit_positive (var 1)) hu
    (le_of_eq_add (d := unit (var 1)*unit (var 1)) (by ipra_ring)) near
  simpa only [crossEquivalent,GaussianEuclideanPointDistance.unit,subst_integralData,GaussianRationalSyntheticDivision.subst_qone,Syn.shift,integral] using
    distance_congr (.eqRefl _) (constant_at (var 0) qone).eqSymm (.eqRefl _) (.eqRefl _) larger

theorem original_Gamma_one_from_integral : Γ ⊢[PRAAx] crossEquivalent GaussianGammaReciprocalInverse.gammaF constantF
    (GaussianGammaReciprocalInverse.gammaData (oneCode : PTm n) one one one) qone :=
  GaussianNameEquivalence.cross_trans _ _ _ _ _ _
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma oneCode one one one
      (.andI unit_lower_source (le_refl one)))) original_integral_one

theorem original_Euler_integral_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    crossEquivalent GaussianEulerImproperName.nameF constantF (integralData : PTm 0) qone := original_integral_one
theorem original_Gamma_unit_from_Euler_integral_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    crossEquivalent GaussianGammaReciprocalInverse.gammaF constantF
      (GaussianGammaReciprocalInverse.gammaData (oneCode : PTm 0) one one one) qone := original_Gamma_one_from_integral

end LeanProofs.IPRA.Analysis.GaussianEulerUnitNormalization
