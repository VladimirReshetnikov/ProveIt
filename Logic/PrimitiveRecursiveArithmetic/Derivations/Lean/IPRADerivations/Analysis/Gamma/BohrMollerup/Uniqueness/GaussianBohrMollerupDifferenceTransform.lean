import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderLinear
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale

/-!
# Exchange and natural scaling of named differences

These identities compare the actual normalized observations to a
common finite rational expression. The proof budgets disappear in the
independent-precision equalities.
-/

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupDifferenceTransform

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (equivalent_of_envelope)
open GaussianNamedDifference (nameF data name_regular sample_error difference_distance)
open GaussianNamedNaturalScaleOrder (cost regular)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_sub)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem raw_exchange (a b c d : PTm n) : Γ ⊢[PRAAx]
    qsub (qsub a b) (qsub c d) ≐ qsub (qsub a c) (qsub b d) :=
  (GaussianNameArithmetic.sum_difference a c (qnegative b) (qnegative d)).eqTrans
    (qadd_congr (.eqRefl _) (GaussianCharacteristicEntryNorm.negative_difference b d))

private theorem double_error (F G H I : PR 2) (x y z w p : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN G y)
    (hz : Γ ⊢[PRAAx] pointCN H z) (hw : Γ ⊢[PRAAx] pointCN I w) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (nameF (nameF F G) (nameF H I)) p (data (data x y) (data z w)))
      (qsub (qsub (ap2 F p x) (ap2 G p y)) (qsub (ap2 H p z) (ap2 I p w))) (num 18) (unit p) := by
  have a := sample_error (nameF F G) (nameF H I) (data x y) (data z w) p
    (name_regular _ _ _ _ hx hy) (name_regular _ _ _ _ hz hw)
  have b := difference_distance _ _ _ _ _ _ _ (unit_positive p)
    (sample_error F G x y p hx hy) (sample_error H I z w p hz hw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) a b)

theorem exchange (F G H I : PR 2) (x y z w : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN G y)
    (hz : Γ ⊢[PRAAx] pointCN H z) (hw : Γ ⊢[PRAAx] pointCN I w) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (nameF F G) (nameF H I)) (nameF (nameF F H) (nameF G I))
      (data (data x y) (data z w)) (data (data x z) (data y w)) := by
  apply equivalent_of_envelope _ _ _ _ (num 36)
    (name_regular _ _ _ _ (name_regular _ _ _ _ hx hy) (name_regular _ _ _ _ hz hw))
    (name_regular _ _ _ _ (name_regular _ _ _ _ hx hz) (name_regular _ _ _ _ hy hw))
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let X := Syn.shift x
  let Y := Syn.shift y
  let Z := Syn.shift z
  let W := Syn.shift w
  let p : PTm (n+1) := var 0
  have hX : Δ ⊢[PRAAx] pointCN F X := by simpa [Δ,X,Fm.shift,Syn.shift] using hx.shift
  have hY : Δ ⊢[PRAAx] pointCN G Y := by simpa [Δ,Y,Fm.shift,Syn.shift] using hy.shift
  have hZ : Δ ⊢[PRAAx] pointCN H Z := by simpa [Δ,Z,Fm.shift,Syn.shift] using hz.shift
  have hW : Δ ⊢[PRAAx] pointCN I W := by simpa [Δ,W,Fm.shift,Syn.shift] using hw.shift
  have a := distance_congr (.eqRefl _) (raw_exchange _ _ _ _) (.eqRefl _) (.eqRefl _)
    (double_error F G H I X Y Z W p hX hY hZ hW)
  have b := distance_symmetric _ _ _ _ (unit_positive p) (double_error F H G I X Z Y W p hX hZ hY hW)
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,Δ,X,Y,Z,W,p] using
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ (unit_positive p) a b)

private def scaleBudget (F G : PR 2) (i x y : PTm n) : PTm n :=
  num 6+(cost F i x+cost G i y)+(cost (nameF F G) i (data x y)+i*num 6)

private theorem scaled_at (F G : PR 2) (i x y p : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN G y) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (nameF (productF F) (productF G)) p (data (productData F i x) (productData G i y)))
      (ap2 (productF (nameF F G)) p (productData (nameF F G) i (data x y)))
      (scaleBudget F G i x y) (unit p) := by
  let f := ap2 F p x
  let g := ap2 G p y
  let D := nameF F G
  let z := data x y
  have hz : Γ ⊢[PRAAx] pointCN D z := name_regular _ _ _ _ hx hy
  have a := sample_error (productF F) (productF G) (productData F i x) (productData G i y) p
    (regular _ _ _ hx) (regular _ _ _ hy)
  have b := difference_distance _ _ _ _ _ _ _ (unit_positive p)
    (GaussianNamedNaturalScaleOrder.sample_error F i x p hx) (GaussianNamedNaturalScaleOrder.sample_error G i y p hy)
  have left := distance_congr (.eqRefl _) (natScale_sub i f g) (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) a b)
  have rhs0 := GaussianNamedNaturalScaleOrder.sample_error D i z p hz
  have norm := GaussianNameBounds.sample_bound D z p hz
  have rhs1 := GaussianNamedNaturalScale.scaled_distance i _ _ _ _ _ (unit_positive p)
    (distance_symmetric _ _ _ _ (unit_positive p) (sample_error F G x y p hx hy)) norm
  have rhs := distance_triangle_same _ _ _ _ _ _ (unit_positive p) rhs0
    (distance_symmetric _ _ _ _ (unit_positive p) rhs1)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) left
    (distance_symmetric _ _ _ _ (unit_positive p) rhs)

theorem scaled_difference (F G : PR 2) (i x y : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN G y) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (productF F) (productF G)) (productF (nameF F G))
      (data (productData F i x) (productData G i y)) (productData (nameF F G) i (data x y)) := by
  apply equivalent_of_envelope _ _ _ _ (scaleBudget F G i x y)
    (name_regular _ _ _ _ (regular _ _ _ hx) (regular _ _ _ hy)) (regular _ _ _ (name_regular _ _ _ _ hx hy))
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let X := Syn.shift x
  let Y := Syn.shift y
  have hX : Δ ⊢[PRAAx] pointCN F X := by simpa [Δ,X,Fm.shift,Syn.shift] using hx.shift
  have hY : Δ ⊢[PRAAx] pointCN G Y := by simpa [Δ,Y,Fm.shift,Syn.shift] using hy.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,scaleBudget,Syn.shift,Δ,X,Y] using
    scaled_at F G (Syn.shift i) X Y (var 0) hX hY

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupDifferenceTransform
