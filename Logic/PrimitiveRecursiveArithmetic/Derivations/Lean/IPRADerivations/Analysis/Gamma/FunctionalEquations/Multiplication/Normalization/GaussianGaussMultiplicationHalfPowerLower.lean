import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.Normalization.GaussianGaussMultiplicationHalfPower
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianRealExponentialCompactLower

/-!
# Strict positivity of the Gauss reciprocal half-power

An explicit positive rational lies below the actual nonnegative-sample
half-power. The bound is transferred through its cross-equivalence with
the exponential of one half of the original logarithm of 1/m.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationHalfPowerLower

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGaussMultiplicationHalfPower
  (halfData halfCoefficient exponentF exponentData ratioPowerF ratioPowerData
    exponent_regular exponent_real half_coefficient_axis half_exponential half_square half_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle)
open GaussianNameArithmetic (multiplyF multiplyData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "HalfF" => GaussianGaussMultiplicationHalfPower.halfF

private def radius (m : PTm n) : PTm n := GaussianNameBounds.U exponentF (exponentData halfCoefficient m)
def lowerDenominator (m : PTm n) : PTm n := pw (num 3) (radius m)
def positiveMargin (m : PTm n) : PTm n := RationalGaussianEmbedding.embed (fraction one (lowerDenominator m))

ipra_subst lowerDenominator [radius, GaussianGaussMultiplicationHalfPower.halfCoefficient]
ipra_subst positiveMargin [fraction]

theorem lower_denominator_positive (m : PTm n) : Γ ⊢[PRAAx] le one (lowerDenominator m) :=
  GaussianFactorBudget.power_positive _ _ (by ipra_le 2)

private theorem decay_order (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    realOrder GaussianEulerIntegrandName.decayF HalfF (GaussianEulerIntegrandName.decayData (radius m) one) (halfData m) := by
  have hi := GaussianGammaFiniteApproximantName.exponential_input exponentF (exponentData halfCoefficient m)
    (exponent_regular halfCoefficient m hm)
  have h := GaussianRealExponentialCompactLower.original_order exponentF (radius m) (exponentData halfCoefficient m)
    hi (exponent_real halfCoefficient m half_coefficient_axis)
  let x := GaussianEulerIntegrandName.decayPoint (radius m) one
  have dec := GaussianRadiusExponentialName.name_regular (Γ := Γ) constantF _ x
    (GaussianGammaFiniteApproximantName.exponential_input constantF x (GaussianGammaCanonicalExponent.constant_regular x))
  exact GaussianNamedRealOrderTransport.transport _ _ ratioPowerF HalfF _ _ (ratioPowerData halfCoefficient m) (halfData m)
    (cross_refl _ _ dec)
    (cross_symm _ _ _ _ (half_exponential m hm)) h

theorem half_lower_at (m p : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    upper (fraction one (lowerDenominator m)) (fstT (ap2 HalfF p (halfData m))) one (unit p) := by
  let K := radius m
  let c := fraction one (lowerDenominator m)
  let y := fstT (ap2 HalfF p (halfData m))
  let t := GaussianNamedRealOrderTransport.precision c y (unit p) two
  have lower := GaussianEulerDecayCompactLower.original_decay_lower (Γ := Γ) t K one K (le_refl one)
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl K))
  have ordered := real_order_at _ _ _ _ t p (decay_order m hm)
  have joined := upper_triangle _ _ _ _ _ _ _ lower ordered
  have budget : Γ ⊢[PRAAx] GaussianNamedRealOrderTransport.upperSlack c y one (unit p) two t :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t)
      (positive_product _ _ (unit_positive t) (unit_positive p))) joined (le_of_eq_add (d := zero) (by ipra_ring))
  exact GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ two budget

theorem half_lower (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] realOrder constantF HalfF (positiveMargin m) (halfData m) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let M := Syn.shift (Syn.shift m)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let a := fraction one (lowerDenominator M)
  have hM : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift] using hm.shift.shift
  have read : Δ ⊢[PRAAx] fstT (ap2 constantF p (positiveMargin M)) ≐ a := by
    have e := (constant_at (Γ := Δ) p (positiveMargin M)).fstE
    exact e.eqTrans (RationalNormalForm.normalize_idempotent _ _ (lower_denominator_positive M))
  have first := RationalValueBounds.upper_one_error (D := unit p)
    (unit_positive q) (le_refl _) (half_lower_at M q hM)
  simpa [realOrder,Δ,M,Syn.shift,p,q] using upper_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) first

def positiveRoot (m : PTm n) : Fm PTm n :=
  pointCN HalfF (halfData m) ⋏
    (realOrder constantF HalfF (positiveMargin m) (halfData m) ⋏
      crossEquivalent (multiplyF HalfF HalfF) constantF (multiplyData HalfF HalfF (halfData m) (halfData m))
        (GaussianPositiveRationalLogarithm.fraction one m))

theorem positive_root (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] positiveRoot m :=
  .andI (half_regular m hm) (.andI (half_lower m hm) (half_square m hm))

theorem actual_reciprocal_half_power_positive_root_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (le one (var 0) ⟶ positiveRoot (var 0)) :=
  closeUniv 1 (.impI (positive_root _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationHalfPowerLower
