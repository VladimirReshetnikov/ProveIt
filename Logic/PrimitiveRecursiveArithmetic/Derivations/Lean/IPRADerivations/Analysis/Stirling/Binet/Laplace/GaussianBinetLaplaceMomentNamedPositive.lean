import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceMomentNamed
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceMomentPositive
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaWeierstrassApproximant
import IPRADerivations.Analysis.Names.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsCaps
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsLog

/-!
# Strict positivity of the actual improper Binet moments on positive names

The fixed [1,2] panel supplies the same positive lower bound at every
rational observation of the input. Its exponential factor depends
on a cap for the real input value. The first Binet kernel summand
supplies the factor 2/104, and every internal time power is at least
one on the panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamedPositive

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentNamed (clock data nameF sample_at frozenData name_regular)
open GaussianBinetLaplaceMomentPositive (marginPoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNamedRightHalfPlane (source radius)
open GaussianNamedRightHalfPlaneSigned (certificate realNumerator imagNumerator denominator sign)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero positive_product)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open RationalValueBounds (upper upper_congr upper_mono)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk Γ t)
local notation "J" => GaussianBinetLaplaceMomentImproper.nameF
local notation "floorDenominator" => GaussianBinetLaplaceRealFloor.floorDenominator

theorem margin_denominator_value (S : PTm n) : Γ ⊢[PRAAx]
    floorDenominator S two ≐ pw (num 3) (S*two)*num 104 := by
  unfold GaussianBinetLaplaceRealFloor.floorDenominator
  exact congrMul (.eqRefl _) (by unfold GaussianBinetKernelRows.lowerDenominator; ipra_ring)

theorem certified_real_cap (q S K : PTm n) (h : Γ ⊢[PRAAx] certificate q S K) :
    Γ ⊢[PRAAx] le (realNumerator q) (S*denominator q) := by
  let X := realNumerator q
  let B := imagNumerator q
  have raw := GaussianLogGammaEulerResidualRadius.native_norm X B (sign q) h.andE₁.andE₁.andE₁.andE₂
  exact nat_sqrt_mono
    (le_trans (le_add_right (X*X) (B*B)) (le_congr raw (.eqRefl _) h.andE₁.andE₂))

theorem observations_floor (f : PR 2) (p x M j : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (marginPoint (radius f x))))
      (fstT (ap2 (nameF f) p (data x M j))) two (unit p) := by
  let k := clock p M j
  let q := ap2 f k x
  let S := radius f x
  let X := realNumerator q
  let D := denominator q
  let y := frozenData f k x j
  let m := marginPoint S
  have hc := GaussianNamedRightHalfPlaneSigned.actual_late f x M k h
    (GaussianBinetLaplaceMomentNamed.clock_margin p M j)
  have cap := certified_real_cap q S (two*M) hc
  have axis := GaussianBinetLaplaceMomentSignedVariation.projected_source q S (two*M) hc
  have order : Γ ⊢[PRAAx] realOrder constantF J m y :=
    GaussianBinetLaplaceMomentPositive.improper_order_with_cap j X D _ S axis cap
  have raw := real_order_at constantF J m y p (succ p) order
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) (succ p)
  have monotone := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_succ_self p)
  have budget : Γ ⊢[PRAAx] le ((unit p+unit (succ p))*unit p) (two*(unit p*unit (succ p))) := by
    ipra_le 𝔞(unit p)*sl monotone
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp hq)
    (upper_congr (.eqRefl _) (congrFst (sample_at f p x M j)).eqSymm (.eqRefl _) (.eqRefl _) raw) budget

theorem named_floor (f : PR 2) (x M j : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] realOrder constantF (nameF f) (marginPoint (radius f x)) (data x M j) := by
  apply order_from_envelope constantF (nameF f) (marginPoint (radius f x)) (data x M j) two
    (constant_regular _) (name_regular f x M j h)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source f (s x) (s M) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianNamedRightHalfPlane.subst_source] using h.shift
  simpa only [envelope,Syn.shift,Δ,s,GaussianBinetLaplaceMomentPositive.subst_marginPoint,
    GaussianNamedRightHalfPlane.subst_radius,GaussianBinetLaplaceMomentNamed.subst_data,
    two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    observations_floor f (var 0) (s x) (s M) (s j) hs

theorem margin_strict (S : PTm n) : Γ ⊢[PRAAx] strictOrder constantF constantF qzero (marginPoint S) := by
  let D := floorDenominator S two
  have hD := GaussianBinetLaplaceRealFloor.floor_denominator_positive (Γ := Γ) S two
  have sep : Γ ⊢[PRAAx] lt (D*zero) (two*one) := by unfold lt; ipra_le 1
  have frac : Γ ⊢[PRAAx] strictOrder constantF constantF (fraction zero one) (fraction two D) :=
    .andI (GaussianStirlingMultiplicativeBoundsLog.constant_order _ _
      (GaussianStirlingMultiplicativeBoundsLog.fractions_order zero one two D (le_refl one) hD (le_of_lt sep)))
      (GaussianStirlingMultiplicativeBoundsCaps.strict_fractions zero one two D (le_refl one) hD sep)
  exact strict_transport _ _ _ _ _ _ _ _
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point zero one (le_refl one)).eqSymm)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point two D hD)) frac

theorem strict_positive (f : PR 2) (x M j : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] strictOrder constantF (nameF f) qzero (data x M j) :=
  GaussianNamedStrictOrderDifference.trans_weak _ _ _ _ _ _ (margin_strict (radius f x)) (named_floor f x M j h)

theorem actual_named_Binet_moment_uniform_strict_positive_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let x := var 0
       let M := var 1
       let j := var 2
       source f x M ⟶
        (realOrder constantF (nameF f) (marginPoint (radius f x)) (data x M j) ⋏
          strictOrder constantF (nameF f) qzero (data x M j))) :=
  closeUniv 3 (.impI (.andI (named_floor f _ _ _ Prf.hyp0) (strict_positive f _ _ _ Prf.hyp0)))

theorem late_sample_floor (f : PR 2) (p x M j : PTm n) (h : Γ ⊢[PRAAx] source f x M)
    (hp : Γ ⊢[PRAAx] le (two*floorDenominator (radius f x) two) (unit p)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction one (floorDenominator (radius f x) two))
      (fstT (ap2 (nameF f) p (data x M j))) := by
  let S := radius f x
  have read := (congrFst (constant_at (Γ := Γ) p (marginPoint S))).eqTrans
    (GaussianBinetLaplaceMomentPositive.margin_scalar S)
  exact GaussianBinetLaplaceMomentFloor.fraction_half_lower_at p _ two _
    (GaussianBinetLaplaceRealFloor.floor_denominator_positive S two) hp
    (upper_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _) (observations_floor f p x M j h))

def floorClock (f : PR 2) (x : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (two*floorDenominator (radius f x) two) zero

theorem positive_observation (f : PR 2) (x M j : PTm n) (h : Γ ⊢[PRAAx] source f x M) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction one (floorDenominator (radius f x) two))
      (fstT (ap2 (nameF f) (floorClock f x) (data x M j))) := by
  let D := two*floorDenominator (radius f x) two
  have hD : Γ ⊢[PRAAx] le D (D*unit zero) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl D) (unit_positive zero))
  exact late_sample_floor f (floorClock f x) x M j h
    (le_trans hD (GaussianFastValueCut.query_budget D zero))

theorem actual_named_Binet_moment_positive_observation_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let x := var 0
       let M := var 1
       let j := var 2
       source f x M ⟶
        RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction one (floorDenominator (radius f x) two))
          (fstT (ap2 (nameF f) (floorClock f x) (data x M j)))) :=
  closeUniv 3 (.impI (positive_observation f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamedPositive
