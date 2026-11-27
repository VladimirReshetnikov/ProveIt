import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.Coefficients.GaussianGammaCanonicalPrefixTaylor

/-!
# All-order shrinking Taylor comparison for the original P sampler

The actual C7 observation is compared to a genuine finite sum of the
original canonical coefficient-name observations. One finite gap removes
only the auxiliary cofinal polynomial query. The physical tail and both
independently requested observations remain in the exact final radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTaylorSampler

open_ipra
open GaussianGammaCanonicalPrefixTaylor (taylor)
open GaussianGammaOriginalPrefixCoefficientVariation (cap)
open GaussianGammaUnitCoefficientMass (budget)
open GaussianRationalHorner (ofGaussian positive_product evaluate)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a b : PTm n) : Fm PTm n := GaussianGammaCanonicalExponent.source z R B ⋏
  (le one b ⋏ (le a b ⋏ bounded (ofGaussian z B) a b))
def numerator (p r R d a b : PTm n) : PTm n :=
  budget (two*R)*pw a (succ d)*unit p*unit r+pw b (succ d)*(succ d*unit p+unit r)
def denominator (p r d b : PTm n) : PTm n := pw b (succ d)*unit p*unit r
def auxiliaryCost (R d : PTm n) : PTm n := one+succ d*cap R d

ipra_subst source
ipra_subst numerator
ipra_subst denominator
ipra_subst auxiliaryCost

theorem denominator_positive (p r d b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    le one (denominator p r d b) :=
  positive_product _ _ (positive_product _ _ (GaussianFactorBudget.power_positive b (succ d) hb) (unit_positive p)) (unit_positive r)

/-- This is the literal full polynomial sampled by the original cofinal program. -/
theorem original_buffer_value (q z R B d : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    evaluate (GaussianGammaOriginalC19Prefix.buffer q R d) (ofGaussian z B) ≐
      GaussianGammaCofinalCoefficientName.sample (GaussianGammaOriginalC19Prefix.stage q d) z (two*R) B :=
  GaussianGammaCofinalCoefficientName.actual_polynomial_observation _ _ _ _ hB

theorem original_auxiliary_error (p r q z R B d a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack
      (qsub (GaussianGammaC7Name.sample p z R B) (taylor r d (ofGaussian z B)))
      (numerator p r R d a b) (denominator p r d b) (auxiliaryCost R d) q := by
  let D := denominator p r d b*unit q
  have hp := unit_positive (Γ := Γ) p
  have hr := unit_positive (Γ := Γ) r
  have hq := unit_positive (Γ := Γ) q
  have hb := h.andE₂.andE₁
  have old := distance_congr (.eqRefl _) (original_buffer_value q z R B d h.andE₁.andE₂.andE₁).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGammaOriginalC19Prefix.original_to_polynomial p q z R B d h.andE₁)
  have finite := GaussianGammaCanonicalPrefixTaylor.original_finite_taylor q r R d (ofGaussian z B) a b
    h.andE₁.andE₁ hb h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂
  have reordered := distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (show Γ ⊢[PRAAx] GaussianGammaCanonicalPrefixTaylor.denominator q r d b ≐ (pw b (succ d)*unit r)*unit q by
      unfold GaussianGammaCanonicalPrefixTaylor.denominator; ipra_ring) finite
  have joined := GaussianRationalDistanceOrder.distance_triangle_common_factor _ _ _ _ _ _ _ _
    hp (positive_product _ _ (GaussianFactorBudget.power_positive b (succ d) hb) hr) hq old reordered
  have arithmetic : Γ ⊢[PRAAx]
      (unit p+unit q)*(pw b (succ d)*unit r)+GaussianGammaCanonicalPrefixTaylor.numerator q r R d a b*unit p ≐
        numerator p r R d a b*unit q+auxiliaryCost R d*denominator p r d b := by
    dsimp only [numerator,auxiliaryCost,denominator,GaussianGammaCanonicalPrefixTaylor.numerator,
      GaussianGammaCanonicalPrefixTaylor.rowNumerator]
    ipra_ring
  have actual : Γ ⊢[PRAAx] distanceBounded (GaussianGammaC7Name.sample p z R B) (taylor r d (ofGaussian z B))
      (numerator p r R d a b*unit q+auxiliaryCost R d*denominator p r d b) D :=
    distance_congr (.eqRefl _) (.eqRefl _) arithmetic (by dsimp only [D,denominator]; ipra_ring) joined
  simpa only [GaussianRationalSlackRemoval.slack,GaussianRationalMetric.distanceBounded,unit,D] using actual

def gapQuery (p r z R B d a b : PTm n) : PTm n := GaussianRationalSlackRemoval.precision
  (qsub (GaussianGammaC7Name.sample p z R B) (taylor r d (ofGaussian z B)))
  (numerator p r R d a b) (denominator p r d b) (auxiliaryCost R d)

/-- Actual P_p against independently requested canonical coefficients c_e(r).
The exact radius is budget(2R)*(a/b)^(d+1)+2^(-p)+(d+1)*2^(-r). -/
theorem original_observations (p r z R B d a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (taylor r d (ofGaussian z B))
      (numerator p r R d a b) (denominator p r d b) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (auxiliaryCost R d) (denominator_positive p r d b h.andE₂.andE₁)
    (original_auxiliary_error p r (gapQuery p r z R B d a b) z R B d a b h)

theorem actual_original_all_order_P_shrinking_taylor_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 6) (var 7) ⟶
      distanceBounded (GaussianGammaC7Name.sample (var 0) (var 2) (var 3) (var 4))
        (taylor (var 1) (var 5) (ofGaussian (var 2) (var 4)))
        (numerator (var 0) (var 1) (var 3) (var 5) (var 6) (var 7)) (denominator (var 0) (var 1) (var 5) (var 7))) :=
  closeUniv 8 (.impI (original_observations _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTaylorSampler
