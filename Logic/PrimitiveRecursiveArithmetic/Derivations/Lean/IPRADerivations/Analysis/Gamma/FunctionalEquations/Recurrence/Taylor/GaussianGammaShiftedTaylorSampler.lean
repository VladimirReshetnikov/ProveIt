import IPRADerivations.Analysis.Gamma.Taylor.FinitePolynomials.GaussianGammaDeflatedFiniteTaylor
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Taylor.GaussianGammaShiftedDeflatedIdentification

/-!
# All-order shrinking Taylor remainder for the original shifted P sampler

The actual shifted C7 sampler is compared with the genuine finite sum
of independently requested canonical c_(e+1) observations. The full
physical shrinking factor survives, without a native inverse multiplier.
Only the auxiliary deflated-polynomial query is removed by a finite gap.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaShiftedTaylorSampler

open_ipra
open GaussianGammaDeflatedPrefixTaylor (deflatedTaylor)
open GaussianGammaOriginalPrefixCoefficientVariation (cap)
open GaussianGammaUnitCoefficientMass (budget)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DName" => GaussianGammaShiftedDeflatedName.nameF

def source (z R B a b : PTm n) : Fm PTm n := GaussianGammaCanonicalExponent.source z R B ⋏
  (le one b ⋏ (le a b ⋏ bounded (ofGaussian z B) a b))
def numerator (p r R d a b : PTm n) : PTm n :=
  budget (two*R)*pw a (succ d)*unit p*unit r+pw b (succ d)*(succ d*unit p+unit r)
def denominator (p r d b : PTm n) : PTm n := pw b (succ d)*unit p*unit r
def auxiliaryCost (R d : PTm n) : PTm n := one+succ d*cap R (succ d)

ipra_subst source
ipra_subst numerator
ipra_subst denominator
ipra_subst auxiliaryCost

theorem denominator_positive (p r d b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] le one (denominator p r d b) :=
  positive_product _ _ (positive_product _ _ (GaussianFactorBudget.power_positive b (succ d) hb) (unit_positive p)) (unit_positive r)

/-- This is the exact original normalized deflated program at its true clock. -/
theorem deflated_name_error (q r z R B d a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 DName q (GaussianGammaShiftedDeflatedName.nameData z R B d)) (deflatedTaylor r d (ofGaussian z B))
      (GaussianGammaDeflatedFiniteTaylor.numerator q r R d a b) (GaussianGammaDeflatedFiniteTaylor.denominator q r d b) := by
  let t := GaussianGammaShiftedDeflatedName.clock q B
  have raw := GaussianGammaDeflatedFiniteTaylor.original_finite_taylor t r R d (ofGaussian z B) a b
    h.andE₁.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂
  have later : Γ ⊢[PRAAx] le q t := le_add_right _ _
  have grow : Γ ⊢[PRAAx] le (unit q) (unit t) := GaussianExponentialReference.unit_monotone later
  have hp := GaussianFactorBudget.power_positive b (succ d) h.andE₂.andE₁
  have oldDen := positive_product _ _ hp (positive_product _ _ (unit_positive t) (unit_positive r))
  have newDen := positive_product _ _ hp (positive_product _ _ (unit_positive q) (unit_positive r))
  have coarse := distance_radius_mono _ _ _ _ (GaussianGammaDeflatedFiniteTaylor.numerator q r R d a b)
    (GaussianGammaDeflatedFiniteTaylor.denominator q r d b) oldDen newDen (by
      dsimp only [GaussianGammaDeflatedFiniteTaylor.numerator,GaussianGammaDeflatedFiniteTaylor.denominator,
        GaussianGammaDeflatedFiniteTaylor.rowNumerator,t,GaussianGammaShiftedDeflatedName.clock] at grow ⊢
      ipra_le (𝔞 (succ d)*𝔞 (pw b (succ d))^2*𝔞 (unit r)^2*𝔞 (cap R (succ d)))*sl grow) raw
  exact distance_congr (GaussianGammaShiftedDeflatedName.name_at q z R B d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) coarse

theorem original_auxiliary_error (p r q z R B d a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack
      (qsub (GaussianGammaShiftedDeflatedPolynomial.shiftedSample p z R B) (deflatedTaylor r d (ofGaussian z B)))
      (numerator p r R d a b) (denominator p r d b) (auxiliaryCost R d) q := by
  let D := denominator p r d b*unit q
  have hp := unit_positive (Γ := Γ) p
  have hr := unit_positive (Γ := Γ) r
  have hq := unit_positive (Γ := Γ) q
  have hb := h.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (denominator_positive p r d b hb) hq
  have first := distance_radius_mono _ _ _ _ (pw b (succ d)*unit r*(unit p+unit q)) D
    (positive_product _ _ hp hq) hD (le_of_eq_add (d := zero) (by dsimp only [D,denominator]; ipra_ring))
    (GaussianGammaShiftedDeflatedIdentification.original_observations p q z R B d h.andE₁)
  have last := distance_radius_mono _ _ _ _ (GaussianGammaDeflatedFiniteTaylor.numerator q r R d a b*unit p) D
    (positive_product _ _ (GaussianFactorBudget.power_positive b (succ d) hb) (positive_product _ _ hq hr)) hD
    (le_of_eq_add (d := zero) (by dsimp only [D,denominator,GaussianGammaDeflatedFiniteTaylor.denominator]; ipra_ring))
    (deflated_name_error q r z R B d a b h)
  have arithmetic : Γ ⊢[PRAAx]
      pw b (succ d)*unit r*(unit p+unit q)+GaussianGammaDeflatedFiniteTaylor.numerator q r R d a b*unit p ≐
        numerator p r R d a b*unit q+auxiliaryCost R d*denominator p r d b := by
    dsimp only [numerator,auxiliaryCost,denominator,GaussianGammaDeflatedFiniteTaylor.numerator,
      GaussianGammaDeflatedFiniteTaylor.rowNumerator]
    ipra_ring
  have actual := distance_congr (.eqRefl _) (.eqRefl _) arithmetic (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first last)
  simpa only [GaussianRationalSlackRemoval.slack,GaussianRationalMetric.distanceBounded,unit,D] using actual

def gapQuery (p r z R B d a b : PTm n) : PTm n := GaussianRationalSlackRemoval.precision
  (qsub (GaussianGammaShiftedDeflatedPolynomial.shiftedSample p z R B) (deflatedTaylor r d (ofGaussian z B)))
  (numerator p r R d a b) (denominator p r d b) (auxiliaryCost R d)

/-- Exact all-order shifted reciprocal remainder, including a zero increment. -/
theorem original_observations (p r z R B d a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaShiftedDeflatedPolynomial.shiftedSample p z R B) (deflatedTaylor r d (ofGaussian z B))
      (numerator p r R d a b) (denominator p r d b) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (auxiliaryCost R d) (denominator_positive p r d b h.andE₂.andE₁)
    (original_auxiliary_error p r (gapQuery p r z R B d a b) z R B d a b h)

theorem actual_original_shifted_P_all_order_shrinking_taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 6) (var 7) ⟶
      distanceBounded (GaussianGammaShiftedDeflatedPolynomial.shiftedSample (var 0) (var 2) (var 3) (var 4))
        (deflatedTaylor (var 1) (var 5) (ofGaussian (var 2) (var 4)))
        (numerator (var 0) (var 1) (var 3) (var 5) (var 6) (var 7)) (denominator (var 0) (var 1) (var 5) (var 7))) :=
  closeUniv 8 (.impI (original_observations _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaShiftedTaylorSampler
