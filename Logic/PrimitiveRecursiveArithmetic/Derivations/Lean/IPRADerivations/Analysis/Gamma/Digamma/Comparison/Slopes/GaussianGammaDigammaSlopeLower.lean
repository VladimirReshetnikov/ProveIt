import IPRADerivations.Analysis.Gamma.Digamma.Comparison.Slopes.GaussianGammaDigammaSlopeLowerFinite
import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaEulerDerivative
import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderEnvelope

/-!
# Lower slope of the original digamma on [1,2]

Matching finite Euler cutoffs yield ψ(x)+(y−x)/4 ≤ ψ(y). The finite
estimate passes through the original native name rates with two
independent observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaSlopeLower

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaEulerDerivative (cutoff_distance)
open GaussianGammaDigammaFiniteSum (reciprocalSum)
open GaussianGammaDigammaSlopeLowerFinite (domain margin sources cutoff_order)
open GaussianGammaFiniteApproximantName (logF)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameRingLaws (add_sample_error sum_left_error)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper upper_of_radius upper_order_right upper_triangle upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

def lowerF : PR 2 := addF DF constantF

def lowerData (a c b : PTm n) : PTm n := addData (dd a b) (margin a c b)

ipra_subst lowerData

theorem sample_envelope (p a c b : PTm n) (h : Γ ⊢[PRAAx] domain a c b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 lowerF p (lowerData a c b))) (fstT (ap2 DF p (dd c b)))
      (a+c+num 23) (unit p) := by
  let N := unit p
  let m := margin a c b
  let T := ap2 logF p N
  let A := qsub T (reciprocalSum a b (succ N))
  let C := qsub T (reciprocalSum c b (succ N))
  have hp := unit_positive (Γ := Γ) p
  have src := sources a c b h
  have addRaw : Γ ⊢[PRAAx] distanceBounded (ap2 lowerF p (lowerData a c b)) (qadd (ap2 DF p (dd a b)) m)
      GaussianNameRingLaws.three N :=
    distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p m)) (.eqRefl _) (.eqRefl _)
      (add_sample_error DF constantF (dd a b) m p (GaussianGammaDigammaNative.name_regular a b src.andE₁) (constant_regular m))
  have hA : Γ ⊢[PRAAx] distanceBounded (ap2 DF p (dd a b)) A (a+num 10) N :=
    cutoff_distance p a b N src.andE₁ (le_refl _)
  have hC : Γ ⊢[PRAAx] distanceBounded (ap2 DF p (dd c b)) C (c+num 10) N :=
    cutoff_distance p c b N src.andE₂ (le_refl _)
  have first := distance_triangle_same _ _ _ _ _ N hp addRaw (sum_left_error _ _ m _ N hp hA)
  have left := upper_order_right _ _ _ _ _
    (upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp first)) (cutoff_order a c b N T h)
  have right := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp (distance_symmetric _ _ _ _ hp hC))
  exact RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _)
    (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (RationalValueBounds.upper_triangle_same hp left right)

/-- The lower slope compares the original digamma names using regular
normalized addition with the exact rational margin. -/
theorem lower_slope (a c b : PTm n) (h : Γ ⊢[PRAAx] domain a c b) :
    Γ ⊢[PRAAx] realOrder lowerF DF (lowerData a c b) (dd c b) := by
  have src := sources a c b h
  have inShift : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift c) (Syn.shift b) := by
    simpa only [Fm.shift,GaussianGammaDigammaSlopeLowerFinite.subst_domain,Syn.shift] using h.shift
  have bound : Γ ⊢[PRAAx] envelope lowerF DF (lowerData a c b) (dd c b) (a+c+num 23) :=
    .allI (by simpa [envelope,Syn.shift] using sample_envelope (var 0) (Syn.shift a) (Syn.shift c) (Syn.shift b) inShift)
  exact order_from_envelope _ _ _ _ _ (add_fast DF constantF _ _
    (GaussianGammaDigammaNative.name_regular a b src.andE₁) (constant_regular _))
    (GaussianGammaDigammaNative.name_regular c b src.andE₂) bound

theorem lower_slope_at (a c b p q : PTm n) (h : Γ ⊢[PRAAx] domain a c b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 lowerF p (lowerData a c b))) (fstT (ap2 DF q (dd c b)))
      (unit p+unit q) (unit p*unit q) :=
  real_order_at _ _ _ _ p q (lower_slope a c b h)

theorem actual_original_digamma_lower_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (domain (var 0) (var 1) (var 2) ⟶
      realOrder lowerF DF (lowerData (var 0) (var 1) (var 2)) (dd (var 1) (var 2))) :=
  closeUniv 3 (.impI (lower_slope _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaSlopeLower
