import IPRADerivations.Analysis.Gamma.Digamma.Comparison.Convexity.GaussianGammaDigammaConvexChords
import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScaleOrder

/-!
# Equal-step convex comparison of the original log Gamma names

The two interior arguments x+1/D and y in [x,y+1/D] have
complementary barycentric weights. Their log Gamma sum is bounded
above by the endpoint sum. The comparison is independent of the
observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaConvexComparison

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaStep (neighborNumerator neighborDenominator neighbor_source)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalNaturalScale (natScale natScale_add natScale_congr natScale_as_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingGammaFractionalIncrementConvexity (gamma_rescale_from scaled_regular scale_cross)
open GaussianStirlingGammaFractionalIncrementObservations (weighted_at weightedCost scalar_upper)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "G" => productF logGammaF
local notation "gd" => productData logGammaF
local notation "lg" => logGammaData

def sumF : PR 2 := addF logGammaF logGammaF
def innerData (a c b D : PTm n) : PTm n :=
  addData (lg (neighborNumerator a b D) (neighborDenominator b D)) (lg c b)
def outerData (a c b D : PTm n) : PTm n :=
  addData (lg a b) (lg (neighborNumerator c b D) (neighborDenominator b D))

ipra_subst innerData [neighborNumerator, neighborDenominator]
ipra_subst outerData [neighborNumerator, neighborDenominator]

theorem inner_regular (a c b D : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN sumF (innerData a c b D) :=
  GaussianNameArithmetic.add_fast _ _ _ _ (log_gamma_regular _ _ (neighbor_source a b D ha hD)) (log_gamma_regular c b hc)

theorem outer_regular (a c b D : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN sumF (outerData a c b D) :=
  GaussianNameArithmetic.add_fast _ _ _ _ (log_gamma_regular a b ha) (log_gamma_regular _ _ (neighbor_source c b D hc hD))

/-- Weighted log-Gamma convexity at a positive rational center on the common denominator. -/
theorem barycenter_order (u v z B r s : PTm n) (hu : Γ ⊢[PRAAx] source u B)
    (hv : Γ ⊢[PRAAx] source v B) (hz : Γ ⊢[PRAAx] source z B) (hr : Γ ⊢[PRAAx] le one r)
    (e : Γ ⊢[PRAAx] r*u+s*v ≐ (r+s)*z) : Γ ⊢[PRAAx]
    realOrder G (addF G G) (gd (r+s) (lg z B))
      (addData (gd r (lg u B)) (gd s (lg v B))) := by
  let k := pred r
  let w := weight k s
  let m := barycenter u v k s
  have ek : Γ ⊢[PRAAx] succ k ≐ r := (pos_of_one_le hr).eqSymm
  have ew : Γ ⊢[PRAAx] w ≐ r+s := by
    unfold w weight
    exact (succ_eq_add_one _).eqTrans
      ((by ipra_ring : Γ ⊢[PRAAx] k+s+one ≐ (k+one)+s).eqTrans
        (congrAdd ((succ_eq_add_one k).eqSymm.eqTrans ek) (.eqRefl _)))
  have ez : Γ ⊢[PRAAx] m ≐ (r+s)*z :=
    (congrAdd (congrMul ek (.eqRefl _)) (.eqRefl _)).eqTrans e
  have hw : Γ ⊢[PRAAx] le one w := zero_lt_succ _
  have hwr : Γ ⊢[PRAAx] le one (r+s) := le_trans hr (le_add_right _ _)
  have hs : Γ ⊢[PRAAx] source m (w*B) :=
    .andI (le_trans (positive_product _ _ (zero_lt_succ k) hu.andE₁) (le_add_right _ _))
      (positive_product _ _ hw hu.andE₂)
  have ec := gamma_rescale_from m (w*B) z B (r+s) hz hwr ez (congrMul ew (.eqRefl _))
  have center := scale_cross w (r+s) (lg m (w*B)) (lg z B) ew
    (log_gamma_regular _ _ hs) (log_gamma_regular _ _ hz) ec
  have uh := log_gamma_regular _ _ hu
  have vr := scaled_regular s (lg v B) (log_gamma_regular _ _ hv)
  have left := scale_cross (succ k) r (lg u B) (lg u B) ek uh uh (cross_refl _ _ uh)
  have pair := add_cross G G G G (gd (succ k) (lg u B)) (gd r (lg u B)) (gd s (lg v B)) (gd s (lg v B))
    (scaled_regular _ _ uh) (scaled_regular _ _ uh) vr vr left (cross_refl _ _ vr)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ center) pair
    (GaussianGammaNativeLogConvexity.weighted_convexity u v B k s hu.andE₁ hv.andE₁ hu.andE₂)

theorem natScale_sum (t x y : PTm n) : Γ ⊢[PRAAx]
    natScale t (qadd x y) ≐ qadd (natScale t x) (natScale t y) :=
  (natScale_as_product _ _).eqTrans ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
    (qadd_congr (natScale_as_product _ _).eqSymm (natScale_as_product _ _).eqSymm))

private theorem exchange_weighted (r s x y : PTm n) : Γ ⊢[PRAAx]
    qadd (qadd (natScale r y) (natScale s x)) (qadd (natScale r x) (natScale s y)) ≐ natScale (r+s) (qadd x y) := by
  have swap := qadd_congr (Γ := Γ) (GaussianReciprocalHorner.qadd_commutative (natScale r y) (natScale s x)) (.eqRefl (qadd (natScale r x) (natScale s y)))
  have join := (GaussianRationalSumAlgebra.qadd_associative (Γ := Γ) (qadd (natScale s x) (natScale r y))
      (natScale r x) (natScale s y)).eqSymm.eqTrans
    (GaussianRationalSumAlgebra.shuffle_four _ _ _ _)
  have same := (natScale_add (Γ := Γ) s r x).eqSymm.eqTrans (natScale_congr (add_comm s r) (.eqRefl _))
  exact swap.eqTrans (join.eqTrans ((qadd_congr same (natScale_add r s y).eqSymm).eqTrans (natScale_sum _ _ _).eqSymm))

private theorem replace_left_log (p a c b D : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (ap2 sumF p (innerData a c b D))
      (qadd (ap2 logGammaF p (lg (neighborNumerator a b D) (neighborDenominator b D)))
        (ap2 logGammaF p (lg (D*c) (neighborDenominator b D)))) (num 5) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  let B := neighborDenominator b D
  let U := lg (neighborNumerator a b D) B
  let V := lg c b
  let W := lg (D*c) B
  have exactLog := gamma_rescale_from (D*c) B c b D hc hD (.eqRefl _) (by unfold B neighborDenominator; ipra_ring)
  have small := GaussianNameEquivalence.cross_diagonal_at p (cross_symm _ _ _ _ exactLog)
  have orig := GaussianNameRingLaws.add_sample_error logGammaF logGammaF U V p (log_gamma_regular _ _ (neighbor_source a b D ha hD))
    (log_gamma_regular _ _ hc)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hp orig
      (GaussianNameRingLaws.sum_right_error (ap2 logGammaF p U) _ _ _ _ hp small))

private theorem replace_right_log (p a c b D : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (ap2 sumF p (outerData a c b D))
      (qadd (ap2 logGammaF p (lg (D*a) (neighborDenominator b D)))
        (ap2 logGammaF p (lg (neighborNumerator c b D) (neighborDenominator b D)))) (num 5) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  let B := neighborDenominator b D
  let U := lg a b
  let V := lg (neighborNumerator c b D) B
  let W := lg (D*a) B
  have exactLog := gamma_rescale_from (D*a) B a b D ha hD (.eqRefl _) (by unfold B neighborDenominator; ipra_ring)
  have small := GaussianNameEquivalence.cross_diagonal_at p (cross_symm _ _ _ _ exactLog)
  have orig := GaussianNameRingLaws.add_sample_error logGammaF logGammaF U V p (log_gamma_regular _ _ ha)
    (log_gamma_regular _ _ (neighbor_source c b D hc hD))
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hp orig
      (GaussianNameRingLaws.sum_left_error _ _ (ap2 logGammaF p V) _ _ hp small))

def gap (a c D : PTm n) : PTm n := D*monus c a
def budget (a c b D : PTm n) : PTm n :=
  num 5+(
    weightedCost (b+gap a c D) b (gap a c D) (lg (neighborNumerator a b D) (neighborDenominator b D))
      (lg (neighborNumerator c b D) (neighborDenominator b D)) (lg (D*a) (neighborDenominator b D))+
    weightedCost (b+gap a c D) b (gap a c D) (lg (D*c) (neighborDenominator b D))
      (lg (D*a) (neighborDenominator b D)) (lg (neighborNumerator c b D) (neighborDenominator b D)))+num 5

ipra_subst budget [gap, weightedCost, GaussianStirlingGammaFractionalIncrementObservations.scaleCost, neighborNumerator, neighborDenominator, GaussianNameRingLaws.three]

set_option maxHeartbeats 800000 in
theorem diagonal_order (p a c b D : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hac : Γ ⊢[PRAAx] le a c) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] upper (fstT (ap2 sumF p (innerData a c b D))) (fstT (ap2 sumF p (outerData a c b D)))
      (budget a c b D) (unit p) := by
  let B := neighborDenominator b D
  let s := gap a c D
  let m := b+s
  let u := D*a
  let v := neighborNumerator c b D
  let l := neighborNumerator a b D
  let r := D*c
  let X := ap2 logGammaF p (lg u B)
  let Y := ap2 logGammaF p (lg v B)
  let L := ap2 logGammaF p (lg l B)
  let R := ap2 logGammaF p (lg r B)
  have hp := unit_positive (Γ := Γ) p
  have hb := positive_product _ _ ha.andE₂ hD
  have hu : Γ ⊢[PRAAx] source u B := .andI (positive_product _ _ hD ha.andE₁) hb
  have hv := neighbor_source c b D hc hD
  have hl := neighbor_source a b D ha hD
  have hr : Γ ⊢[PRAAx] source r B := .andI (positive_product _ _ hD hc.andE₁) hb
  have eqL : Γ ⊢[PRAAx] b*v+s*u ≐ m*l := by
    have e := natEq (eq_add_of_le hac)
    unfold u v l m s gap neighborNumerator
    apply deriveNat
    ipra_simps
    linear_combination (𝔞 b*𝔞 D)*e
  have eqR : Γ ⊢[PRAAx] b*u+s*v ≐ m*r := by
    have e := natEq (eq_add_of_le hac)
    unfold u v r m s gap neighborNumerator
    apply deriveNat
    ipra_simps
    linear_combination -(𝔞 b*𝔞 D)*e
  have Xr := log_gamma_regular _ _ hu
  have Yr := log_gamma_regular _ _ hv
  have Lr := log_gamma_regular _ _ hl
  have Rr := log_gamma_regular _ _ hr
  have le1 := weighted_at p m b s (lg l B) (lg v B) (lg u B) Lr Yr Xr
    (barycenter_order v u l B b s hv hu hl ha.andE₂ eqL)
  have le2 := weighted_at p m b s (lg r B) (lg u B) (lg v B) Rr Xr Yr
    (barycenter_order u v r B b s hu hv hr ha.andE₂ eqR)
  have le3 := GaussianStirlingTailComparison.point_add_upper_same _ _ _ _ _ _ _ hp le1 le2
  have cl := upper_congr (congrFst (natScale_sum m L R).eqSymm) (congrFst (exchange_weighted b s X Y))
    (.eqRefl _) (.eqRefl _) le3
  have cm := GaussianRationalNaturalScaleOrder.reflect_upper m (qadd L R) (qadd X Y) _ (unit p) cl
  have hm : Γ ⊢[PRAAx] le one m := le_trans ha.andE₂ (le_add_right _ _)
  let A := weightedCost m b s (lg l B) (lg v B) (lg u B)+weightedCost m b s (lg r B) (lg u B) (lg v B)
  have grow := le_congr (one_mul (unit p)) (.eqRefl _) (mul_le_mul_right (unit p) hm)
  have mid : Γ ⊢[PRAAx] upper (fstT (qadd L R)) (fstT (qadd X Y)) A (unit p) :=
    RationalValueBounds.upper_mono_den (positive_product _ _ hm hp) grow cm
  have left := scalar_upper _ _ _ _ hp (replace_left_log p a c b D ha hc hD)
  have right := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp (replace_right_log p a c b D ha hc hD))
  have middle := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left mid) right
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hp) hp)
    middle (le_of_eq_add (d := zero) (by dsimp only [budget,A,B,l,r,m,s,u,v]; ipra_ring))

set_option maxHeartbeats 800000 in
theorem log_comparison_at (p q a c b D : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hac : Γ ⊢[PRAAx] le a c) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] upper (fstT (ap2 sumF p (innerData a c b D))) (fstT (ap2 sumF q (outerData a c b D)))
      (unit p+unit q) (unit p*unit q) := by
  let x := innerData a c b D
  let y := outerData a c b D
  let K := budget a c b D+two
  let t := precision (fstT (ap2 sumF p x)) (fstT (ap2 sumF q y)) (unit p*unit q) K
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have ht := unit_positive (Γ := Γ) t
  have hi := GaussianNameEquivalence.point_at sumF x p t (inner_regular a c b D ha hc hD)
  have ho := GaussianNameEquivalence.point_at sumF y t q (outer_regular a c b D ha hc hD)
  have left := scalar_upper _ _ _ _ (positive_product _ _ hp ht) hi
  have mid := diagonal_order t a c b D ha hc hac hD
  have right := scalar_upper _ _ _ _ (positive_product _ _ ht hq) ho
  have chain := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left mid) right
  apply remove_upper_slack _ _ _ _ K
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hp ht) ht)
    (positive_product _ _ ht hq)) chain
  exact le_of_eq_add (d := zero) (by unfold K; ipra_ring)

theorem log_comparison (a c b D : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hac : Γ ⊢[PRAAx] le a c) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] realOrder sumF sumF (innerData a c b D) (outerData a c b D) := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  refine .allI (.allI ?_)
  have ha' : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using ha.shift.shift
  have hc' : Δ ⊢[PRAAx] source (sh c) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hc.shift.shift
  have ac' : Δ ⊢[PRAAx] le (sh a) (sh c) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hac.shift.shift
  have d' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hD.shift.shift
  simpa only [realOrder,sh,Syn.shift,subst_innerData,subst_outerData] using log_comparison_at (var 1) (var 0) _ _ _ _ ha' hc' ac' d'

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaConvexComparison
