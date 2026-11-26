import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaNativeMidpointLogGap
import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaWeightedMidpointGrouping
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialMajorant
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerDenominator

/-!
# A positive weighted margin for the native rational log-Gamma chord

A single pair consisting of one copy of each endpoint supplies the
midpoint margin. Both positive weights are written as successors, so
all remaining terms are nonnegative natural multiplicities.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNativeWeightedLogGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerMidpointLogHeadGap (margin)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLogOrder (add_order order_refl add_interleave)
open GaussianGammaNativeLogConvexityCore (nativeCenterData nativeWeightedData)
open GaussianGammaWeightedMidpointGrouping
  (first_group second_group groupNumerator groupWeight groupData midpointData group_numerator_positive group_denominator_positive)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast multiply_one_left add_associative)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianStirlingGammaFractionalIncrementConvexity (scaled_regular)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => productF logGammaF
local notation "gd" => productData logGammaF
local notation "C" => constantF

def centerData (a d b r s : PTm n) : PTm n :=
  addData (margin a d) (nativeCenterData a d b r (succ s))
def weightedData (a d b r s : PTm n) : PTm n := nativeWeightedData a d b r (succ s)

private theorem scale_one (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (productF f) f (productData f one x) x := by
  have oneCross : Γ ⊢[PRAAx] crossEquivalent C oneF (naturalPoint one) x := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast _)
    refine .allI ?_
    simpa [Syn.shift] using ((constant_at (var 0) (naturalPoint (one : PTm (n+1)))).eqTrans
      (GaussianGammaEulerDenominator.natural_one.eqTrans (one_at (var 0) (Syn.shift x)).eqSymm))
  have first := GaussianGammaAdjacentCutoff.multiply_cross C oneF f f (naturalPoint one) x x x
    (constant_regular _) (one_fast _) hf hf oneCross (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ first (multiply_one_left f x hf)

theorem add_scale_succ (f : PR 2) (r x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (addF f (productF f)) (productF f)
      (addData x (productData f r x)) (productData f (succ r) x) := by
  let a : PTm n := naturalPoint one
  let b := naturalPoint r
  let c := naturalPoint (succ r)
  let H := productF f
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have hc := constant_regular (Γ := Γ) c
  have h1 := GaussianNameArithmetic.multiply_fast C f a x ha hf
  have h2 := GaussianNameArithmetic.multiply_fast C f b x hb hf
  have left := add_cross f H H H x (productData f one x) (productData f r x) (productData f r x)
    hf h1 h2 h2 (cross_symm _ _ _ _ (scale_one f x hf)) (cross_refl _ _ h2)
  have split := GaussianNameRingLaws.right_distributive C C f a b x ha hb hf
  have sum : Γ ⊢[PRAAx] crossEquivalent (addF C C) C (addData a b) c := constant_sum a b c ((GaussianRationalLinearProduct.qadd_commutative a b).eqTrans
    (GaussianPositiveExponentialMajorant.natural_successor_sum r))
  have right := GaussianGammaAdjacentCutoff.multiply_cross (addF C C) C f f (addData a b) c x x
    (add_fast _ _ _ _ ha hb) hc hf hf sum (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split) right)

private theorem add_group (F H J L : PR 2) (x y z w : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN H y)
    (hz : Γ ⊢[PRAAx] pointCN J z) (hw : Γ ⊢[PRAAx] pointCN L w) :
    Γ ⊢[PRAAx] crossEquivalent (addF F (addF (addF H J) L)) (addF (addF F H) (addF J L))
      (addData x (addData (addData y z) w)) (addData (addData x y) (addData z w)) := by
  have hYZ := add_fast _ _ _ _ hy hz
  have hXY := add_fast _ _ _ _ hx hy
  have hXYZ := add_fast _ _ _ _ hXY hz
  have a := cross_symm _ _ _ _ (add_associative F (addF H J) L x (addData y z) w hx hYZ hw)
  have b := add_cross (addF F (addF H J)) (addF (addF F H) J) L L
    (addData x (addData y z)) (addData (addData x y) z) w w
    (add_fast _ _ _ _ hx hYZ) hXYZ hw hw
    (cross_symm _ _ _ _ (add_associative F H J x y z hx hy hz)) (cross_refl _ _ hw)
  have c := add_associative (addF F H) J L (addData x y) z w hXY hz hw
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b c)

theorem weighted_order (a d b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder (addF C G) (addF G G) (centerData a d b r s) (weightedData a d b r s) := by
  let x := logGammaData a b
  let y := logGammaData d b
  let m := midpointData a d b
  let z := nativeCenterData a d b r (succ s)
  let k := gd (groupWeight r) (groupData a d b r)
  let A := gd r x
  let B := gd s y
  let M := gd two m
  let c := margin a d
  have hx := log_gamma_regular a b (.andI ha hb)
  have hy := log_gamma_regular d b (.andI hd hb)
  have hm := log_gamma_regular (a+d) (two*b)
    (.andI (le_trans ha (le_add_right _ _)) (positive_product _ _ RationalAlgebra.two_positive hb))
  have hM := scaled_regular two m hm
  have hA := scaled_regular r x hx
  have hB := scaled_regular s y hy
  have hC := constant_regular (Γ := Γ) c
  have ord₁ := first_group a d b r ha hb
  have ord₂ := second_group a d b r s ha hd hb
  have widen := add_order G (addF G G) G G k (addData M A) B B ord₁ (order_refl _ _ hB)
  have chain := GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ ord₂ widen
  have withMargin := add_order C C G (addF (addF G G) G) c c z (addData (addData M A) B)
    (order_refl _ _ hC) chain
  have regrouped := GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (add_fast _ _ _ _ hC
      (scaled_regular (weight r (succ s)) (logGammaData (barycenter a d r (succ s)) (weight r (succ s)*b))
        (log_gamma_regular _ _ (.andI
          (GaussianGammaEulerRationalLogConvexity.center_positive a d r (succ s) ha)
          (GaussianGammaEulerRationalLogConvexity.center_denominator_positive b r (succ s) hb))))))
    (add_group C G G G c M A B hC hM hA hB) withMargin
  have applyGap := add_order (addF C G) (addF logGammaF logGammaF) (addF G G) (addF G G)
    (addData c M) (addData x y) (addData A B) (addData A B)
    (GaussianGammaNativeMidpointLogGap.midpoint_order a d b ha hd hb)
    (order_refl _ _ (add_fast _ _ _ _ hA hB))
  have ordered := GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ regrouped applyGap
  have interchange := add_interleave logGammaF logGammaF G G x y A B hx hy hA hB
  have endpoint := add_cross _ G _ G _ (gd (succ r) x) _ (gd (succ s) y)
    (add_fast _ _ _ _ hx hA) (scaled_regular _ _ hx) (add_fast _ _ _ _ hy hB) (scaled_regular _ _ hy)
    (add_scale_succ logGammaF r x hx) (add_scale_succ logGammaF s y hy)
  have hCenter := GaussianGammaEulerRationalLogConvexity.center_positive a d r (succ s) ha
  have hDen := GaussianGammaEulerRationalLogConvexity.center_denominator_positive b r (succ s) hb
  have hz := scaled_regular (weight r (succ s)) (logGammaData (barycenter a d r (succ s)) (weight r (succ s)*b))
    (log_gamma_regular _ _ (.andI hCenter hDen))
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (add_fast _ _ _ _ hC hz)) (cross_trans _ _ _ _ _ _ interchange endpoint) ordered

theorem actual_positive_rational_log_Gamma_weighted_margin_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 0) ⋏ (le one (var 1) ⋏ le one (var 2))) ⟶ realOrder (addF C G) (addF G G)
      (centerData (var 0) (var 1) (var 2) (var 3) (var 4))
      (weightedData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (weighted_order _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNativeWeightedLogGap
