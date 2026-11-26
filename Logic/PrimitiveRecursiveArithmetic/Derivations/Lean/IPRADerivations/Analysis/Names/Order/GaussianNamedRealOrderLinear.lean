import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary
import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaStrongLogConvexityAlgebra
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScaleOrder

/-!
# Strictly positive rational scaling and sign reversal of real name order

An exact natural denominator cancels the fractional coefficient.
Negation reverses order by adding the two opposite names and cancelling
each common sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianNamedRealOrderLinear

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaStrongLogConvexityAlgebra (add_negative_front)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast recode_congr)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_at add_associative)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero qmul)
open GaussianRationalMetric (qsub qsub_canonical)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSyntheticDivision (qsub_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF

theorem negative_constant_at (c p : PTm n) : Γ ⊢[PRAAx]
    ap2 (negativeF C) p (negativeData c) ≐ qsub qzero c :=
  (negative_at C c p).eqTrans
    ((recode_congr (qsub_congr (.eqRefl _) (constant_at _ c))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qsub_canonical _ _)))

theorem negative_constant (c : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (negativeF C) C (negativeData c) (qsub qzero c) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (negative_fast _ _ (constant_regular _)) (constant_regular _)
  refine .allI ?_
  simpa [Syn.shift] using (negative_constant_at (Γ := Γ.map Fm.shift) (Syn.shift c) (var 0)).eqTrans
    (constant_at (var 0) (qsub qzero (Syn.shift c))).eqSymm

theorem negative_order (F J : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (hj : Γ ⊢[PRAAx] pointCN J y) (h : Γ ⊢[PRAAx] realOrder F J x y) :
    Γ ⊢[PRAAx] realOrder (negativeF J) (negativeF F) (negativeData y) (negativeData x) := by
  let A := negativeF J
  let B := negativeF F
  let a := negativeData y
  let b := negativeData x
  have ha := negative_fast J y hj
  have hb := negative_fast F x hf
  have l := add_order A A F J a a x y (order_refl _ _ ha) h
  have both := add_order (addF A F) (addF A J) B B (addData a x) (addData a y) b b l (order_refl _ _ hb)
  have left := GaussianNamedStrictOrderDifference.sum_sub_right A F a x ha hf
  have right := cross_trans _ _ _ _ _ _ (add_associative A J B a y b ha hj hb)
    (add_negative_front J B y b hj hb)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left) right both

def fractionData (f : PR 2) (r b x : PTm n) : PTm n := multiplyData C f (fraction r b) x

theorem fractional_regular (f : PR 2) (r b x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (productF f) (fractionData f r b x) := multiply_fast _ _ _ _ (constant_regular _) h

theorem scaled_fraction (f : PR 2) (r b x : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (productF (productF f)) (productF f) (productData (productF f) b (fractionData f r b x))
      (productData f r x) := by
  let B := naturalPoint b
  let R := fraction r b
  let U := naturalPoint r
  have hB := constant_regular (Γ := Γ) B
  have hR := constant_regular (Γ := Γ) R
  have hU := constant_regular (Γ := Γ) U
  have step := GaussianNameRingLaws.multiply_associative C C f B R x hB hR h
  have point := cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross B R)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (GaussianGammaRationalUnscaledChord.fraction_cancels r b hb))
  have fold := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF C C) C f f
    (multiplyData C C B R) U x x (multiply_fast _ _ _ _ hB hR) hU h h point (cross_refl _ _ h)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ step) fold

theorem fractional_order (f g : PR 2) (r b x y : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] realOrder (productF f) (productF g) (fractionData f r b x) (fractionData g r b y) := by
  apply GaussianNamedNaturalScaleOrder.reflect_order _ _ b _ _ hb
    (fractional_regular f r b x hf) (fractional_regular g r b y hg)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (scaled_fraction f r b x hb hf)
    (cross_symm _ _ _ _ (scaled_fraction g r b y hb hg))
    (GaussianNamedNaturalScaleOrder.preserve_order f g r x y hf hg h)

end LeanProofs.IPRA.Analysis.GaussianNamedRealOrderLinear
