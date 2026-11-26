import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaDyadicLocation
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaPositiveLower
import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianNamedEulerLogarithmicFrozenRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTangent

/-!
# The dyadic digamma location as an original named Euler input

The location samples are exact axis fractions in [1,2]. The original
right-half-plane source uses margin one. Freezing the original named
logarithmic integral therefore recovers the native integral at the
same dyadic argument, with its original independent observation rate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationInput

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaDyadicLocation (index location locationF location_at location_regular lower selected_cell)
open GaussianGammaDigammaDyadicMesh (grid grid_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNamedRightHalfPlane (actual_late_source certificate denominator marginPoint numerator radius threshold)
open GaussianRationalHorner (canonical canonical_congr ofGaussian ofGaussian_canonical)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingGammaLogarithm (arg euler_real_source)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalGaussianEmbedding (axis axis_congr)
open RationalValueBounds (upper_of_order)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "L" => locationF
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "LF" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "ld" => GaussianNamedEulerLogarithmicImproper.data

theorem lower_bound (p : PTm n) : Γ ⊢[PRAAx] le (grid p) (lower p) := le_add_right _ _

theorem upper_bound (p : PTm n) : Γ ⊢[PRAAx] le (lower p) (two*grid p) := by
  have h := le_of_lt (selected_cell (Γ := Γ) p).andE₁
  unfold lower
  ipra_le sl h

theorem rational_source (p : PTm n) : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (lower p) (grid p) :=
  .andI (le_trans (grid_positive p) (lower_bound p)) (grid_positive p)

theorem real_at (p x : PTm n) : Γ ⊢[PRAAx] canonical (ap2 L p x) ⋏ axis (ap2 L p x) :=
  .andI (canonical_congr (location_at p x) (ofGaussian_canonical _ _ (grid_positive p)))
    (axis_congr (location_at p x).eqSymm (GaussianStirlingNames.fraction_axis (lower p) (grid p) (grid_positive p)))

theorem named_real_samples (x : PTm n) : Γ ⊢[PRAAx] realSamples L x :=
  .allI (real_at (var 0) (Syn.shift x))

private theorem above_one (p : PTm n) :
    Γ ⊢[PRAAx] rationalLE (fstT (marginPoint one)) (fstT (location p)) := by
  have bound := fractions_order (Γ := Γ) one one (lower p) (grid p) (le_refl one) (grid_positive p)
    (by ipra_le sl (lower_bound p))
  exact rationalLE_congr (congrFst (GaussianRationalExponentialTangent.fraction_one one (le_refl one))) (.eqRefl _) bound

theorem named_certificate (x : PTm n) : Γ ⊢[PRAAx] certificate L x one := by
  refine order_from_envelope constantF L (marginPoint one) x zero (constant_regular _) (location_regular x) (.allI ?_)
  let p : PTm (n+1) := var 0
  let y := Syn.shift x
  have ready := rationalLE_congr (congrFst (constant_at p (marginPoint one))).eqSymm
    (congrFst (location_at p y)).eqSymm (above_one (Γ := Γ.map Fm.shift) p)
  simpa [envelope,Syn.shift,p,y,one] using upper_of_order _ _ (zero : PTm (n+1)) (unit p) ready

theorem named_source (x : PTm n) : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source L x one :=
  .andI (location_regular x) (.andI (le_refl one) (named_certificate x))

theorem named_real_source (x : PTm n) : Γ ⊢[PRAAx] GaussianNamedGammaPositiveLower.source L x one :=
  .andI (named_source x) (named_real_samples x)

theorem frozen_fraction_at (p x : PTm n) : Γ ⊢[PRAAx]
    ofGaussian (numerator L p x) (denominator L p x) ≐ location p :=
  (GaussianExponentialReference.recode_fixed _ (real_at p x).andE₁).eqTrans (location_at p x)

def nativeLogData (j k : PTm n) : PTm n :=
  GaussianEulerLogarithmicImproperName.data j (arg (lower k)) (lower k) (grid k) (grid k)

ipra_subst nativeLogData

theorem frozen_log_cross (j k x : PTm n) (hLate : Γ ⊢[PRAAx] le (threshold one) k) :
    Γ ⊢[PRAAx] crossEquivalent IF IF (GaussianNamedEulerLogarithmicFrozenRate.frozenData L j x one k)
      (nativeLogData j k) := by
  exact GaussianEulerLogarithmicImproperInputProperness.original_improper_proper j _ _ _ _ _ _ _ _
    (.andI (actual_late_source L x one k (named_source x) hLate)
      (.andI (euler_real_source _ _ (rational_source k)).andE₁ (frozen_fraction_at k x)))

theorem frozen_log_rate (s j k x : PTm n) (hLate : Γ ⊢[PRAAx] le (threshold one) k)
    (hDemand : Γ ⊢[PRAAx] le (succ (GaussianEulerLogarithmicContinuity.modulus s j (radius L x) (two*one))) k) :
    Γ ⊢[PRAAx] independentRate (LF L) IF (ld j x one) (nativeLogData j k) (num 5) (unit s) := by
  have rate := GaussianNamedEulerLogarithmicFrozenRate.frozen_rate L s j x one k
    (.andI (named_source x) (.andI hLate hDemand))
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive s) rate
    (cross_refl _ _ (GaussianNamedEulerLogarithmicImproper.name_regular L j x one (named_source x)))
    (cross_symm _ _ _ _ (frozen_log_cross j k x hLate))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationInput
