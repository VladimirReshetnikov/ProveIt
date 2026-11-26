import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteCutoffParts
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerIntegralGammaIdentification

/-!
# Variation bounds for both actual incomplete Euler cutoffs

Only the appropriate original tail is added when either cutoff moves.
Sampling the earlier and later names at independent precisions costs
the original tail bound and a fixed multiple of the dyadic errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCutoffRate

open_ipra
open GaussianEulerIncompleteCutoff (clock)
open GaussianEulerIncompleteCutoffParts (lowerData upperData piece_sources)
open GaussianEulerCompactAdditivity (nameF)
open GaussianEulerCutoffCauchyComparison (combined)
open GaussianGammaIntegralCutoffs (height)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNameArithmetic (addData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans point_at)
open GaussianRationalHorner (positive_product qzero qadd)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (p q K H : PTm n) : PTm n := K*unit p*unit q+H*(unit q+num 5*unit p)
def denominator (p q H : PTm n) : PTm n := H*unit p*unit q

private theorem from_added_tail (p q x y u K H : PTm n)
    (hH : Γ ⊢[PRAAx] le one H)
    (h : Γ ⊢[PRAAx] crossEquivalent nameF GaussianEulerIncompleteCutoffParts.sumF y (addData x u))
    (hx : Γ ⊢[PRAAx] pointCN nameF x) (hu : Γ ⊢[PRAAx] pointCN nameF u)
    (hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 nameF q x))
    (ht : Γ ⊢[PRAAx] bounded (ap2 nameF q u) (K*unit q+H) (H*unit q)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p y) (ap2 nameF q x) (numerator p q K H) (denominator p q H) := by
  let P := unit p
  let Q := unit q
  let D := denominator p q H
  let v := ap2 nameF q x
  let w := ap2 nameF q u
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hH hP) hQ
  have hHQ := positive_product _ _ hH hQ
  have first := distance_radius_mono _ _ _ _ ((P+Q)*H) D (positive_product _ _ hP hQ) hD
    (le_of_eq_add (d := zero) (by dsimp only [D, denominator]; ipra_ring)) (cross_at _ _ _ _ p q h)
  have sample := GaussianNameRingLaws.add_sample_error nameF nameF x u q hx hu
  have second := distance_radius_mono _ _ _ _ (num 3*H*P) D hQ hD
    (le_of_eq_add (d := zero) (by dsimp only [D, denominator, GaussianNameRingLaws.three]; ipra_ring)) sample
  have htail := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hHQ).iffMpr ht
  have sum := GaussianNameArithmetic.sum_distance v v w qzero zero (K*Q+H) (H*Q) hHQ
    (GaussianRationalPowerDifference.distance_refl_zero _ _ hHQ) htail
  have last₀ : Γ ⊢[PRAAx] distanceBounded (qadd v w) v (K*Q+H) (H*Q) :=
    distance_congr (.eqRefl _) (GaussianRationalLinearProduct.qadd_zero_right v hc)
    (by ipra_ring) (.eqRefl _) sum
  have last := distance_radius_mono _ _ _ _ ((K*Q+H)*P) D hHQ hD
    (le_of_eq_add (d := zero) (by dsimp only [D, denominator]; ipra_ring)) last₀
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first (distance_triangle_same _ _ _ _ _ _ hD second last))

theorem original_cutoff_piece_observations (p q s k j z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hk : Γ ⊢[PRAAx] le (clock s a b) k) (hj : Γ ⊢[PRAAx] lt k j) :
    Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (lowerData z R B j A a b)) (ap2 nameF q (lowerData z R B k A a b))
      (numerator p q (combined A R) (unit (height k A R))) (denominator p q (unit (height k A R))) ⋏
    distanceBounded (ap2 nameF p (upperData z R B j A a b)) (ap2 nameF q (upperData z R B k A a b))
      (numerator p q (combined A R) (unit (height k A R))) (denominator p q (unit (height k A R))) := by
  let H := unit (height k A R)
  let Q := unit q
  let K := combined A R
  let hA := h.andE₁.andE₁
  let hj' := le_of_lt hj
  let hD := h.andE₁.andE₂.andE₁
  have source : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z R B A a b :=
    .andI hD (.andI hA (.andI ha hb))
  have split : Γ ⊢[PRAAx] GaussianGammaCompactCutoffSplit.source z R B k j A := .andI hD (.andI hA hj')
  have old := piece_sources s k z R B A a b source hk
  have lreg := GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ old.andE₁
  have ureg := GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ old.andE₂
  have ltreg := GaussianGammaCompactCutoffSplit.lower_regular z R B k j A split
  have utreg := GaussianGammaCompactCutoffSplit.upper_regular z R B k j A split
  have lower := GaussianEulerIncompleteCutoffParts.original_lower_cutoff_change s k j z R B A a b source hk hj
  have upper := GaussianEulerIncompleteCutoffParts.original_upper_cutoff_change s k j z R B A a b source hk hj
  have reorder := GaussianNameRingLaws.add_commutative nameF nameF _ _ ltreg lreg
  have lower' := cross_trans _ _ _ _ _ _ lower reorder
  have hH := unit_positive (Γ := Γ) (height k A R)
  have hQ := unit_positive (Γ := Γ) q
  have den := positive_product _ _ hH hQ
  have low := GaussianEulerNamedLowerTail.lower_observation_bound q z R B k j A (.andI hD h.andE₁) hj'
  have high := GaussianEulerNamedUpperTail.original_named_upper_tail q z R B k j A split
  have eqCoeff := GaussianEulerUpperTailCauchyBudget.exact_tail_coefficient (Γ := Γ) R
  have low' := bounded_radius_mono _ _ _ (K*Q+H) (H*Q) den den
    (mul_le_mul_right (H*Q) (add_le_add_right H (mul_le_mul_right Q (le_add_right A (GaussianGammaIntegralCutoffs.tailCoefficient R))))) low
  have high' := bounded_radius_mono _ _ _ (K*Q+H) (H*Q) den den
    (mul_le_mul_right (H*Q) (add_le_add_right H (mul_le_mul_right Q
      (le_congr eqCoeff (.eqRefl _) (le_add_left (GaussianGammaIntegralCutoffs.tailCoefficient R) A))))) high
  exact .andI
    (from_added_tail p q _ _ _ K H hH lower' lreg ltreg
      (GaussianCompactRiemannName.name_canonical GaussianEulerIntegrandName.evaluatorF q _ _ _ _ _ _) low')
    (from_added_tail p q _ _ _ K H hH upper ureg utreg
      (GaussianCompactRiemannName.name_canonical GaussianEulerIntegrandName.evaluatorF q _ _ _ _ _ _) high')

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteCutoffRate
