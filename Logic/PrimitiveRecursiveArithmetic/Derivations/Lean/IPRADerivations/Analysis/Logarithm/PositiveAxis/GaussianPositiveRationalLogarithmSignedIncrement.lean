import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmIncrement
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmVariation
import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddCoefficients
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference

/-!
# Signed first-order increments of the original rational logarithm

The first-order term is the literal rational difference multiplied by
the reciprocal of the base point. For the decreasing case the original
forward estimate is based at the other endpoint. The two candidate
linear terms differ by the squared increment divided by the product
of the endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmSignedIncrement

open_ipra
open ComplexLogarithmRemainder (scale oneCode normSq_scale normSq_one)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (cross_at)
open GaussianNamedDifference (difference_distance)
open GaussianPositiveRationalLogarithm (data logF sample source fraction sample_congr)
open GaussianPositiveRationalLogarithmIncrement (increment errorNumerator errorDenominator original_increment)
open GaussianPositiveRationalLogarithmProperness (original_logarithm_proper)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same reversed_difference)
open GaussianRationalHorner (qadd qmul ofGaussian_canonical ofGaussian_represents positive_product)
open GaussianRationalMetric (qsub qnegative distanceBounded bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_sub_cancel qsub_congr qmul_congr)
open GaussianStirlingOddCoefficients (fraction_equal fraction_product fraction_add_same)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.Variance (ad)
open RationalHarmonicIntervalVariation (gap)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def observed (p q a b c d : PTm n) : PTm n := qsub (sample p c d) (sample q a b)
def linear (a b c d : PTm n) : PTm n := qmul (qsub (fraction c d) (fraction a b)) (fraction b a)

def budget (p q R A D T : PTm n) : PTm n :=
  (two*((R*A)*(R*A)))*(unit p*unit q)+(T*(D*D))*(unit p+unit q)
def denominator (p q D : PTm n) : PTm n := (D*D)*(unit p*unit q)

private theorem fraction_congr {a b c d : PTm n}
    (h : Γ ⊢[PRAAx] a ≐ c) (k : Γ ⊢[PRAAx] b ≐ d) : Γ ⊢[PRAAx] fraction a b ≐ fraction c d :=
  GaussianCompactRiemannName.fraction_congr _ _ _ _ h k

private theorem fraction_step (a k b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qsub (fraction (a+k) b) (fraction a b) ≐ fraction k b :=
  (qsub_congr (fraction_add_same a k b hb).eqSymm (.eqRefl _)).eqTrans
    (qadd_sub_cancel _ _ (ofGaussian_canonical _ _ hb))

private theorem local_size {a b k R A D : PTm n} (hl : Γ ⊢[PRAAx] le b (R*a))
    (hs : Γ ⊢[PRAAx] le (D*k) (A*b)) : Γ ⊢[PRAAx] le (D*k) ((R*A)*a) :=
  le_trans hs (le_congr (mul_comm _ _) (by ipra_ring) (mul_le_mul_right A hl))

private theorem abs_gap_of_order (a c : PTm n) (h : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx] ad a c ≐ monus c a := by
  change Γ ⊢[PRAAx] monus a c + monus c a ≐ monus c a
  exact (congrAdd h (.eqRefl _)).eqTrans (zero_add _)

private theorem ratio_distance (a c k : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hc : Γ ⊢[PRAAx] le one c) (he : Γ ⊢[PRAAx] a ≐ c+k) :
    Γ ⊢[PRAAx] distanceBounded (fraction k c) (fraction k a) (k*k) (a*c) := by
  let E := a*c
  have hE := positive_product a c ha hc
  have first : Γ ⊢[PRAAx] fraction k c ≐ fraction (k*a) E := fraction_equal _ _ _ _ hc hE (by dsimp [E]; ipra_ring)
  have second : Γ ⊢[PRAAx] fraction k a ≐ fraction (k*c) E := fraction_equal _ _ _ _ ha hE (by dsimp [E]; ipra_ring)
  have sizes : Γ ⊢[PRAAx] k*a ≐ k*c+k*k := by
    exact (congrMul (.eqRefl k) he).eqTrans (by ipra_ring)
  have diff : Γ ⊢[PRAAx] qsub (fraction k c) (fraction k a) ≐ fraction (k*k) E :=
    (qsub_congr (first.eqTrans (fraction_congr sizes (.eqRefl _))) second).eqTrans (fraction_step _ _ _ hE)
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (scale (k*k) oneCode) ≐ (k*k)*(k*k) :=
    (normSq_scale _ _).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
  apply bound_congr diff.eqSymm (.eqRefl _) (.eqRefl _)
  exact bounded_of_cleared _ _ E _ E hE hE (ofGaussian_represents _ _ hE)
    (le_congr (congrMul (.eqRefl _) norm).eqSymm (by ipra_ring) (le_refl ((E*E)*((k*k)*(k*k)))))

private theorem original_radius (p q a b k R A D : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] le one D) (hs : Γ ⊢[PRAAx] le (D*k) ((R*A)*a)) :
    Γ ⊢[PRAAx] distanceBounded (increment p q a b k) (fraction k a)
      (((R*A)*(R*A))*(unit p*unit q)+(D*D)*(unit p+unit q)) (denominator p q D) := by
  let P := unit p
  let Q := unit q
  have hU := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have h := le_mul_mono hs hs
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ ha ha) hU)
    (positive_product _ _ (positive_product _ _ hD hD) hU)
    (by dsimp only [errorNumerator,errorDenominator,denominator]
        ipra_le (𝔞(P)^2)*(𝔞(Q)^2)*sl h using dsimp only [P,Q]; ring)
    (original_increment p q a b k ha hb)

private theorem increasing (p q a c b R A D : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D)
    (hl : Γ ⊢[PRAAx] le b (R*a)) (ho : Γ ⊢[PRAAx] le a c)
    (hs : Γ ⊢[PRAAx] le (D*ad a c) (A*b)) :
    Γ ⊢[PRAAx] distanceBounded (observed p q a b c b) (linear a b c b) (budget p q R A D one) (denominator p q D) := by
  let k := monus c a
  have he : Γ ⊢[PRAAx] c ≐ a+k := eq_add_of_le ho
  have hg := le_congr (congrMul (.eqRefl _) (abs_gap_of_order a c ho)) (.eqRefl _) hs
  have simple := original_radius p q a b k R A D ha hb hD (local_size hl hg)
  have dx : Γ ⊢[PRAAx] increment p q a b k ≐ observed p q a b c b :=
    qsub_congr (sample_congr p b he.eqSymm) (.eqRefl _)
  have dy : Γ ⊢[PRAAx] linear a b c b ≐ fraction k a :=
    (qmul_congr ((qsub_congr (fraction_congr he (.eqRefl _)) (.eqRefl _)).eqTrans (fraction_step _ _ _ hb))
      (.eqRefl _)).eqTrans ((fraction_product _ _ _ _ hb ha).eqTrans (fraction_equal _ _ _ _ (positive_product _ _ hb ha) ha (by ipra_ring)))
  have dh := positive_product _ _ (positive_product _ _ hD hD) (positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q))
  exact distance_radius_mono _ _ _ _ _ _ dh dh
    (mul_le_mul_right (denominator p q D) (le_of_eq_add (d := (R*A)*(R*A)*(unit p*unit q)) (by unfold budget; ipra_ring)))
    (distance_congr dx dy.eqSymm (.eqRefl _) (.eqRefl _) simple)

private theorem decreasing (p q a c b R A D : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] le one D) (hl : Γ ⊢[PRAAx] le b (R*a)) (hr : Γ ⊢[PRAAx] le b (R*c))
    (ho : Γ ⊢[PRAAx] le c a) (hs : Γ ⊢[PRAAx] le (D*ad a c) (A*b)) :
    Γ ⊢[PRAAx] distanceBounded (observed p q a b c b) (linear a b c b) (budget p q R A D one) (denominator p q D) := by
  let k := monus a c
  let T := (R*A)*(R*A)
  let P := unit p
  let Q := unit q
  let E := denominator p q D
  have he : Γ ⊢[PRAAx] a ≐ c+k := eq_add_of_le ho
  have gap : Γ ⊢[PRAAx] ad a c ≐ k :=
    (add_comm _ _).eqTrans (abs_gap_of_order c a ho)
  have hg := le_congr (congrMul (.eqRefl _) gap) (.eqRefl _) hs
  have hleft := local_size hl hg
  have hright := local_size hr hg
  have hU := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (positive_product _ _ hD hD) hU
  have hE' := positive_product _ _ (positive_product _ _ hD hD) (positive_product _ _ (unit_positive (Γ := Γ) q) (unit_positive p))
  have first := GaussianNamedDifference.negative_distance _ _ _ _ hE' (original_radius q p c b k R A D hc hb hD hright)
  have dx : Γ ⊢[PRAAx] qnegative (increment q p c b k) ≐ observed p q a b c b :=
    (reversed_difference _ _).eqTrans (qsub_congr (.eqRefl _) (sample_congr q b he.eqSymm))
  have stepEq : Γ ⊢[PRAAx] qsub (fraction a b) (fraction c b) ≐ fraction k b :=
    (qsub_congr (fraction_congr he (.eqRefl _)) (.eqRefl _)).eqTrans (fraction_step _ _ _ hb)
  have reverseStep : Γ ⊢[PRAAx] qsub (fraction c b) (fraction a b) ≐ qnegative (fraction k b) :=
    (reversed_difference (fraction a b) (fraction c b)).eqSymm.eqTrans
      (RationalGaussianEmbedding.negative_congr stepEq)
  have scaled : Γ ⊢[PRAAx] qmul (fraction k b) (fraction b a) ≐ fraction k a :=
    (fraction_product _ _ _ _ hb ha).eqTrans (fraction_equal _ _ _ _ (positive_product _ _ hb ha) ha (by ipra_ring))
  have dy : Γ ⊢[PRAAx] linear a b c b ≐ qnegative (fraction k a) :=
    (qmul_congr reverseStep (.eqRefl (fraction b a))).eqTrans
      ((GaussianInverseBinomialRows.negative_product (fraction k b) (fraction b a)).eqSymm.eqTrans
        (RationalGaussianEmbedding.negative_congr scaled))
  have main : Γ ⊢[PRAAx] distanceBounded (observed p q a b c b) (qnegative (fraction k c))
      (T*(P*Q)+(D*D)*(P+Q)) E := distance_congr dx (.eqRefl _) (by dsimp [T,P,Q]; ipra_ring)
    (by dsimp [E,denominator]; ipra_ring) first
  have correction := GaussianNamedDifference.negative_distance _ _ _ _ (positive_product _ _ ha hc)
    (ratio_distance a c k ha hc he)
  have pay := le_mul_mono hleft hright
  have changeOfBase : Γ ⊢[PRAAx] distanceBounded (qnegative (fraction k c)) (linear a b c b) (T*(P*Q)) E :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ha hc) hE
      (by dsimp only [T,P,Q,E,denominator]
          ipra_le (𝔞(unit p)*𝔞(unit q))*sl pay using ring)
      (distance_congr (.eqRefl _) dy.eqSymm (.eqRefl _) (.eqRefl _) correction)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp [T,P,Q,budget]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE main changeOfBase)

theorem common_denominator (p q a c b R A D : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] le one D) (hl : Γ ⊢[PRAAx] le b (R*a)) (hr : Γ ⊢[PRAAx] le b (R*c))
    (hs : Γ ⊢[PRAAx] le (D*ad a c) (A*b)) :
    Γ ⊢[PRAAx] distanceBounded (observed p q a b c b) (linear a b c b) (budget p q R A D one) (denominator p q D) := by
  refine .orE (le_total a c) ?_ ?_
  · exact increasing p q a c b R A D ha.wk hb.wk hD.wk hl.wk Prf.hyp0 hs.wk
  · exact decreasing p q a c b R A D ha.wk hc.wk hb.wk hD.wk hl.wk hr.wk Prf.hyp0 hs.wk

theorem original_observations (p q a b c d R A D : PTm n)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d)
    (hD : Γ ⊢[PRAAx] le one D) (hl : Γ ⊢[PRAAx] le b (R*a)) (hr : Γ ⊢[PRAAx] le d (R*c))
    (hclose : Γ ⊢[PRAAx] le (D*gap a b c d) (A*b*d)) :
    Γ ⊢[PRAAx] distanceBounded (observed p q a b c d) (linear a b c d)
      (budget p q R A D (one+two)) (denominator p q D) := by
  let aa := a*d
  let cc := b*c
  let bb := b*d
  let P := unit p
  let Q := unit q
  let E := denominator p q D
  have haa := positive_product _ _ hab.andE₁ hcd.andE₂
  have hcc := positive_product _ _ hab.andE₂ hcd.andE₁
  have hbb := positive_product _ _ hab.andE₂ hcd.andE₂
  have hleft : Γ ⊢[PRAAx] le bb (R*aa) := le_congr (.eqRefl _) (by dsimp [aa]; ipra_ring) (mul_le_mul_right d hl)
  have hright : Γ ⊢[PRAAx] le bb (R*cc) :=
    le_congr (mul_comm _ _) (by dsimp [cc]; ipra_ring) (mul_le_mul_right b hr)
  have hsize : Γ ⊢[PRAAx] le (D*ad aa cc) (A*bb) := le_congr (.eqRefl _) (by dsimp [bb]; ipra_ring) hclose
  have core := common_denominator p q aa cc bb R A D haa hcc hbb hD hleft hright hsize
  have ea : Γ ⊢[PRAAx] a*bb ≐ b*aa := by dsimp [aa,bb]; ipra_ring
  have ec : Γ ⊢[PRAAx] c*bb ≐ d*cc := by dsimp [cc,bb]; ipra_ring
  have fa := fraction_equal a b aa bb hab.andE₂ hbb (ea.eqTrans (mul_comm _ _))
  have fc := fraction_equal c d cc bb hcd.andE₂ hbb (ec.eqTrans (mul_comm _ _))
  have fi := fraction_equal b a bb aa hab.andE₁ haa (by dsimp [aa,bb]; ipra_ring)
  have lin : Γ ⊢[PRAAx] linear a b c d ≐ linear aa bb cc bb := qmul_congr (qsub_congr fc fa) fi
  have left := cross_at logF logF _ _ q q (original_logarithm_proper a b aa bb hab (.andI haa hbb) ea)
  have right := cross_at logF logF _ _ p p (original_logarithm_proper c d cc bb hcd (.andI hcc hbb) ec)
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hq : Γ ⊢[PRAAx] le one Q := unit_positive q
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (positive_product _ _ hD hD) (positive_product _ _ hp hq)
  have ra : Γ ⊢[PRAAx] distanceBounded (sample q a b) (sample q aa bb) ((two*(D*D))*P) E :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hq hq) hE
      (le_of_eq_add (d := zero) (by dsimp [E,denominator,P,Q]; ipra_ring)) left
  have rc : Γ ⊢[PRAAx] distanceBounded (sample p c d) (sample p cc bb) ((two*(D*D))*Q) E :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hE
      (le_of_eq_add (d := zero) (by dsimp [E,denominator,P,Q]; ipra_ring)) right
  have near := difference_distance _ _ _ _ _ _ _ hE rc ra
  exact distance_congr (.eqRefl _) lin.eqSymm (by dsimp [budget,P,Q]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE near core)

theorem original_observations_of_radius (p q a b c d R A D : PTm n)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d)
    (hD : Γ ⊢[PRAAx] le one D) (hl : Γ ⊢[PRAAx] le b (R*a)) (hr : Γ ⊢[PRAAx] le d (R*c))
    (hclose : Γ ⊢[PRAAx] RationalValueBounds.radius (RationalCubeMidpoint.fraction a b)
      (RationalCubeMidpoint.fraction c d) A D) :
    Γ ⊢[PRAAx] distanceBounded (observed p q a b c d) (linear a b c d)
      (budget p q R A D (one+two)) (denominator p q D) :=
  original_observations p q a b c d R A D hab hcd hD hl hr
    (GaussianPositiveRationalLogarithmVariation.original_time_distance a b c d A D hab.andE₂ hcd.andE₂ hD hclose)

def input (a b c d R A D : PTm n) : Fm PTm n :=
  source a b ⋏ (source c d ⋏ (le one D ⋏ (le b (R*a) ⋏ (le d (R*c) ⋏ le (D*gap a b c d) (A*b*d)))))

theorem actual_original_signed_rational_logarithm_first_order_remainder_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded (observed (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (linear (var 2) (var 3) (var 4) (var 5)) (budget (var 0) (var 1) (var 6) (var 7) (var 8) (one+two))
          (denominator (var 0) (var 1) (var 8))) :=
  closeUniv 9 (.impI (original_observations _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmSignedIncrement
