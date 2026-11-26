import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalSlackRemoval

/-!
# Independent raw observations of an actual nested three-name sum

The original normalized addition programs use their actual two nested
queries. Genuine component regularity compares those later observations
to one shared requested raw query. One computed finite rational gap
removes four auxiliary dyadics, retaining one outer and three component
observation allowances. No regularity of the left name is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedThreeSumObservations

open_ipra
open GaussianNameArithmetic (addF addData add_fast)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at point_at)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def raw (F G H : PR 2) (q x y z : PTm n) : PTm n := qadd (ap2 F q x) (qadd (ap2 G q y) (ap2 H q z))
def sumData (x y z : PTm n) : PTm n := addData x (addData y z)
def numerator (p q : PTm n) : PTm n := unit q+num 3*unit p
def denominator (p q : PTm n) : PTm n := unit p*unit q
def source (K F G H : PR 2) (w x y z : PTm n) : Fm PTm n :=
  pointCN F x ⋏ (pointCN G y ⋏ (pointCN H z ⋏ crossEquivalent K (addF F (addF G H)) w (sumData x y z)))

ipra_subst raw
ipra_subst sumData
ipra_subst numerator
ipra_subst denominator
ipra_subst source

theorem original_sum_regular (F G H : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) (hh : Γ ⊢[PRAAx] pointCN H z) : Γ ⊢[PRAAx]
    pointCN (addF F (addF G H)) (sumData x y z) := add_fast _ _ _ _ hf (add_fast _ _ _ _ hg hh)

theorem nested_sample_at (F G H : PR 2) (s x y z : PTm n) : Γ ⊢[PRAAx]
    ap2 (addF F (addF G H)) s (sumData x y z) ≐
      qadd (ap2 F (GaussianFastValueCut.exponent two s) x)
        (qadd (ap2 G (GaussianFastValueCut.exponent two (GaussianFastValueCut.exponent two s)) y)
          (ap2 H (GaussianFastValueCut.exponent two (GaussianFastValueCut.exponent two s)) z)) :=
  (GaussianExponentialReference.add_sample F (addF G H) x (addData y z) s).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (GaussianExponentialReference.add_sample G H y z _))

private theorem later_observations (F : PR 2) (x k q s : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hk : Γ ⊢[PRAAx] le s k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F k x) (ap2 F q x) (unit s+unit q) (unit s*unit q) := by
  have grow := GaussianExponentialReference.unit_monotone hk
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive k) (unit_positive q))
    (positive_product _ _ (unit_positive s) (unit_positive q)) (by ipra_le (𝔞(unit q)^2)*sl grow) (point_at F x k q hf)

private theorem original_slack (K F G H : PR 2) (p q s w x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) (hh : Γ ⊢[PRAAx] pointCN H z)
    (he : Γ ⊢[PRAAx] crossEquivalent K (addF F (addF G H)) w (sumData x y z)) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 K p w) (raw F G H q x y z)) (numerator p q) (denominator p q) (num 4) s := by
  let k := GaussianFastValueCut.exponent two s
  let l := GaussianFastValueCut.exponent two k
  have sk : Γ ⊢[PRAAx] le s k := le_add_right _ _
  have sl : Γ ⊢[PRAAx] le s l := le_trans sk (le_add_right _ _)
  have d := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive q)
  have triple := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ d (later_observations F x k q s hf sk)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ d (later_observations G y l q s hg sl) (later_observations H z l q s hh sl))
  have rawNear : Γ ⊢[PRAAx] distanceBounded (ap2 (addF F (addF G H)) s (sumData x y z))
      (raw F G H q x y z) (num 3*(unit s+unit q)) (unit s*unit q) :=
    distance_congr (nested_sample_at F G H s x y z).eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) triple
  let D := denominator p q*unit s
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive s)
  have first := distance_radius_mono _ _ _ _ ((unit p+unit s)*unit q) D
    (positive_product _ _ (unit_positive p) (unit_positive s)) hd
    (le_of_eq_add (d := zero) (by dsimp only [D,denominator]; ipra_ring)) (cross_at _ _ _ _ p s he)
  have last := distance_radius_mono _ _ _ _ (num 3*(unit s+unit q)*unit p) D d hd
    (le_of_eq_add (d := zero) (by dsimp only [D,denominator]; ipra_ring)) rawNear
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [numerator,denominator,unit]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd first last)

def gapQuery (K F G H : PR 2) (p q w x y z : PTm n) : PTm n :=
  GaussianRationalSlackRemoval.precision (qsub (ap2 K p w) (raw F G H q x y z)) (numerator p q) (denominator p q) (num 4)

theorem original_observations (K F G H : PR 2) (p q w x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) (hh : Γ ⊢[PRAAx] pointCN H z)
    (he : Γ ⊢[PRAAx] crossEquivalent K (addF F (addF G H)) w (sumData x y z)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 K p w) (raw F G H q x y z) (numerator p q) (denominator p q) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (num 4) (positive_product _ _ (unit_positive p) (unit_positive q))
    (original_slack K F G H p q (gapQuery K F G H p q w x y z) w x y z hf hg hh he)

theorem actual_original_three_sum_independent_observations_closed (K F G H : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source K F G H (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (ap2 K (var 0) (var 2)) (raw F G H (var 1) (var 3) (var 4) (var 5))
        (numerator (var 0) (var 1)) (denominator (var 0) (var 1))) :=
  closeUniv 6 (.impI (original_observations K F G H _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedThreeSumObservations
