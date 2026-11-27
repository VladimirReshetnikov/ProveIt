import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.Slopes.GaussianGammaNegativeCriticalSlope
import IPRADerivations.Analysis.Gamma.Digamma.Comparison.Slopes.GaussianGammaDigammaSlopeLower
import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerRationalLogOrder

/-!
# Quarter lower slope of the shifted negative-interval digamma

The finite correction is increasing on the entire open interval.
Adding its exact order to the original positive digamma lower slope
keeps the same rational displacement margin.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLowerSlope

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerRationalLogOrder (add_order)
open GaussianGammaNegativeCriticalCorrection (correction guard)
open GaussianGammaNegativeCriticalCorrectionSlope (ordered correction_monotone denominator_positive)
open GaussianGammaNegativeCriticalEndpoints (nameF nameData name_regular shifted_source)
open GaussianGammaNegativeCriticalSlope (left_guard right_guard)
open GaussianNameArithmetic (addF addData add_fast add_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl cross_trans cross_to_diagonal)
open GaussianNameRingLaws (add_associative add_commutative add_sample_error three)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderTransport (transport)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingMultiplicativeBoundsLog (constant_order)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "CF" => constantF

def lowerF : PR 2 := addF nameF CF
def margin (a c b : PTm n) : PTm n := fraction (monus c a) (num 4*b)
def lowerData (a c b N : PTm n) : PTm n := addData (nameData a b N) (margin a c b)

ipra_subst margin
ipra_subst lowerData

private theorem positive_domain (a c b : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] GaussianGammaDigammaSlopeLowerFinite.domain (b+a) (b+c) b :=
  .andI (denominator_positive a c b h)
    (.andI (le_add_right _ _) (.andI (by ipra_le sl h.andE₂.andE₁) (by ipra_le sl (le_of_lt h.andE₂.andE₂))))

private theorem margin_recode (a c b : PTm n) :
    Γ ⊢[PRAAx] margin a c b ≐ GaussianGammaDigammaSlopeLowerFinite.margin (b+a) (b+c) b :=
  GaussianCompactRiemannName.fraction_congr _ _ _ _
    ((congrMonus (add_comm b c) (add_comm b a)).eqTrans (monus_add_add c a b)).eqSymm (.eqRefl _)

private theorem swap_constants (x g m d : PTm n)
    (hx : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN DF x) (e : Γ ⊢[PRAAx] g ≐ m) :
    Γ ⊢[PRAAx] crossEquivalent (addF (addF DF CF) CF) (addF (addF DF CF) CF)
      (addData (addData x d) g) (addData (addData x m) d) := by
  let CC := addF CF CF
  let l := addData d g
  let r := addData m d
  have xₗ := add_associative DF CF CF x d g hx (constant_regular d) (constant_regular g)
  have xᵣ := add_associative DF CF CF x m d hx (constant_regular m) (constant_regular d)
  have g_m := GaussianSignedNameExponentialOrder.constant_equal_cross g m e
  have swap := add_commutative (Γ := Γ) CF CF d g (constant_regular d) (constant_regular g)
  have equal := add_equivalent CF CF CF CF g m d d (constant_regular g) (constant_regular m)
    (constant_regular d) (constant_regular d) (cross_to_diagonal _ _ _ _ g_m)
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ (constant_regular d)))
  have inner : Γ ⊢[PRAAx] crossEquivalent CC CC l r :=
    cross_trans _ _ _ _ _ _ swap equal
  have middle := add_equivalent DF DF CC CC x x l r hx hx
    (add_fast _ _ _ _ (constant_regular d) (constant_regular g))
    (add_fast _ _ _ _ (constant_regular m) (constant_regular d))
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ hx)) (cross_to_diagonal _ _ _ _ inner)
  exact cross_trans _ _ _ _ _ _ xₗ (cross_trans _ _ _ _ _ _ middle (cross_symm _ _ _ _ xᵣ))

theorem lower_slope (a c b N : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] realOrder lowerF nameF (lowerData a c b N) (nameData c b N) := by
  let g := margin a c b
  let m := GaussianGammaDigammaSlopeLowerFinite.margin (b+a) (b+c) b
  let x := dd (b+a) b
  let d := correction a b N
  let e := correction c b N
  let pF := GaussianGammaDigammaSlopeLower.lowerF
  let pD := GaussianGammaDigammaSlopeLower.lowerData (b+a) (b+c) b
  have hp := GaussianGammaDigammaSlopeLower.lower_slope (b+a) (b+c) b (positive_domain a c b h)
  have hc := constant_order d e (correction_monotone a c b N h)
  have total := add_order pF DF CF CF pD (dd (b+c) b) d e hp hc
  have left : Γ ⊢[PRAAx] crossEquivalent lowerF lowerF (lowerData a c b N) (addData pD d) :=
    swap_constants x g m d (GaussianGammaDigammaNative.name_regular _ _ (shifted_source _ _ (left_guard a c b h)))
      (margin_recode a c b)
  exact transport _ _ _ _ _ _ _ _ left
    (cross_refl _ _ (name_regular c b N (right_guard a c b h))) total

theorem lower_at (p q a c b N : PTm n) (h : Γ ⊢[PRAAx] ordered a c b) :
    Γ ⊢[PRAAx] upper
      (RationalArithmetic.add (fstT (ap2 nameF p (nameData a b N))) (fstT (margin a c b)))
      (fstT (ap2 nameF q (nameData c b N))) (num 4*unit q+unit p) (unit p*unit q) := by
  let x := nameData a b N
  let y := nameData c b N
  let m := margin a c b
  let v := ap2 nameF p x
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have err : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (ap2 lowerF p (lowerData a c b N)) (qadd v m)
      three (unit p) :=
    distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p m)) (.eqRefl _) (.eqRefl _)
      (add_sample_error nameF CF x m p (name_regular a b N (left_guard a c b h)) (constant_regular m))
  have raw := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp err)
  have observed := real_order_at lowerF nameF (lowerData a c b N) y p q (lower_slope a c b N h)
  have joined := upper_triangle _ _ _ _ _ _ _ raw observed
  have scale := upper_mono _ _ _ _ (num 4*unit q+unit p) (unit p*unit q)
    (positive_product _ _ hp (positive_product _ _ hp hq)) joined (by unfold three; ipra_le 0)
  exact upper_congr (RationalGaussianRealPart.real_add v m) (.eqRefl _) (.eqRefl _) (.eqRefl _) scale

theorem original_shifted_negative_digamma_lower_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ordered (var 0) (var 1) (var 2) ⟶
      realOrder lowerF nameF (lowerData (var 0) (var 1) (var 2) (var 3)) (nameData (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (lower_slope _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLowerSlope
