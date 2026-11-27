import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.FrozenRates.GaussianNamedEulerLogarithmicFrozenRate
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput
import IPRADerivations.Analysis.Euler.Logarithms.Improper.GaussianEulerLogarithmicZeroIdentification

/-!
# Order-zero logarithmic integration on the original fixed complex name

One actual decoded input meets both original continuity demands. The
logarithmic and Gamma programs retain their independent output clocks.
At that common native input the checked order-zero integral is Gamma.
The three genuine observation comparisons give twelve auxiliary dyadics;
original regularity and the existing rational finite gap remove them.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicZeroIdentification

open_ipra
open GaussianNamedRightHalfPlane (source threshold radius)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "ldata" => GaussianNamedEulerLogarithmicImproper.data
local notation "G" => GaussianNamedGamma.nameF
local notation "gdata" => GaussianNamedGamma.data

def commonClock (f : PR 2) (t x A : PTm n) : PTm n := threshold A+
  (succ (GaussianEulerLogarithmicContinuity.modulus t zero (radius f x) (two*A))+
    succ (GaussianGammaHalfPlaneInputContinuity.modulus t (radius f x) (two*A)))

ipra_subst commonClock

theorem logarithmic_source (f : PR 2) (t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianNamedEulerLogarithmicFrozenRate.source f t zero x A (commonClock f t x A) := by
  have margin : Γ ⊢[PRAAx] le (threshold A) (commonClock f t x A) := le_add_right _ _
  have demand : Γ ⊢[PRAAx] le (succ (GaussianEulerLogarithmicContinuity.modulus t zero (radius f x) (two*A)))
      (commonClock f t x A) := le_trans (le_add_right _ _) (le_add_left _ _)
  exact .andI h (.andI margin demand)

theorem gamma_source (f : PR 2) (t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianNamedGammaLateInput.input f t (commonClock f t x A) x A := by
  have margin : Γ ⊢[PRAAx] le (threshold A) (commonClock f t x A) := le_add_right _ _
  have demand : Γ ⊢[PRAAx] le (succ (GaussianGammaHalfPlaneInputContinuity.modulus t (radius f x) (two*A)))
      (commonClock f t x A) := le_trans (le_add_left _ _) (le_add_left _ _)
  exact .andI h (.andI margin demand)

theorem native_order_zero (f : PR 2) (t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEulerLogarithmicImproperName.nameF GaussianGammaReciprocalInverse.gammaF
      (GaussianNamedEulerLogarithmicFrozenRate.frozenData f zero x A (commonClock f t x A))
      (GaussianNamedGammaLateInput.encodedData f (commonClock f t x A) x A) :=
  GaussianEulerLogarithmicZeroIdentification.original_logarithmic_order_zero_is_Gamma _ _ _ _
    (GaussianNamedGammaLateInput.encoded_source f t (commonClock f t x A) x A (gamma_source f t x A h))

theorem original_diagonal (f : PR 2) (t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (L f) t (ldata zero x A)) (ap2 (G f) t (gdata x A)) (num 12) (unit t) := by
  let U := unit t
  have hU := unit_positive (Γ := Γ) t
  have left := GaussianNamedEulerLogarithmicFrozenRate.frozen_observations f t t t zero x A
    (commonClock f t x A) (logarithmic_source f t x A h)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 (L f) t (ldata zero x A))
      (ap2 GaussianEulerLogarithmicImproperName.nameF t
        (GaussianNamedEulerLogarithmicFrozenRate.frozenData f zero x A (commonClock f t x A))) (num 7) U :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hU) hU
      (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,U]; ipra_ring)) left
  have center := cross_at _ _ _ _ t t (native_order_zero f t x A h)
  have middle : Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianEulerLogarithmicImproperName.nameF t
        (GaussianNamedEulerLogarithmicFrozenRate.frozenData f zero x A (commonClock f t x A)))
      (ap2 GaussianGammaReciprocalInverse.gammaF t
        (GaussianNamedGammaLateInput.encodedData f (commonClock f t x A) x A)) two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hU
      (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring)) center
  have right := GaussianNamedGammaLateInput.original_observations f t t t (commonClock f t x A) x A
    (gamma_source f t x A h)
  have last : Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianGammaReciprocalInverse.gammaF t
        (GaussianNamedGammaLateInput.encodedData f (commonClock f t x A) x A))
      (ap2 (G f) t (gdata x A)) (num 3) U :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hU) hU
      (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,U]; ipra_ring))
      (distance_symmetric _ _ _ _ (denominator_positive _ _ _ hU) right)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first (distance_triangle_same _ _ _ _ _ _ hU middle last))

theorem original_order_zero_is_Gamma (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    crossEquivalent (L f) (G f) (ldata zero x A) (gdata x A) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 12)
    (GaussianNamedEulerLogarithmicImproper.name_regular f zero x A h) (GaussianNamedGamma.name_regular f x A h)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift A) := by
    simpa only [Fm.shift,GaussianNamedRightHalfPlane.subst_source,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianNamedEulerLogarithmicImproper.subst_data,
    GaussianNamedGamma.subst_data,Syn.shift,PTm.subst_num,ConciseIPRA.PTm.subst_zero] using
    original_diagonal f (var 0) (Syn.shift x) (Syn.shift A) hs

theorem original_observations (f : PR 2) (p q x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (L f) p (ldata zero x A)) (ap2 (G f) q (gdata x A))
      (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_order_zero_is_Gamma f x A h)

theorem actual_original_named_order_zero_is_Gamma_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source f (var 0) (var 1) ⟶ crossEquivalent (L f) (G f)
      (ldata zero (var 0) (var 1)) (gdata (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_order_zero_is_Gamma f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicZeroIdentification
