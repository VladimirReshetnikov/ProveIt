import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaNativeWeightedLogGap
import IPRADerivations.Analysis.Stirling.Bounds.Multiplicative.GaussianStirlingMultiplicativeBoundsCaps
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Logarithms.GaussianEulerUnitLogarithmicMargin

/-!
# Strict log convexity for positive rational Gamma arguments

The explicit positive margin excludes reverse order between the
weighted native logarithm names. All comparison arguments and
weights are internal natural codes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNativeStrictLogConvexity

open_ipra
open ComplexLogarithmRemainder (scale oneCode zeroCode)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerMidpointHeadGap (large gap gap_square)
open GaussianGammaEulerMidpointLogHeadGap (margin margin_source)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaNativeLogConvexity (weighted_convexity)
open GaussianGammaNativeLogConvexityCore (nativeCenterData nativeWeightedData)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_associative add_negative add_zero zeroF zero_at zero_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product qzero)
open GaussianStirlingGammaFractionalIncrementConvexity (scaled_regular)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "G" => productF logGammaF

private theorem fraction_zero : Γ ⊢[PRAAx] qzero ≐ fraction (zero : PTm n) one := by
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal zeroCode (scale (zero : PTm n) oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_zero,
        GaussianRootAlgebra.im_zero,IPRA.Q.mk_zero]
  exact GaussianRationalHorner.canonical_unique _ _ _ one (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _))
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl _)
    (GaussianRationalHorner.represents_congr (.eqRefl _) native (.eqRefl _) (GaussianRationalHorner.zero_represents one))
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))

private theorem zero_constant (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent zeroF C x (fraction zero one) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast _) (constant_regular _)
  refine .allI ?_
  simpa [Syn.shift] using ((zero_at (var 0) (Syn.shift x)).eqTrans
    ((fraction_zero (n := n+1)).eqTrans (constant_at (var 0) (fraction zero one)).eqSymm))

theorem cancel_order (F : PR 2) (c x : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (h : Γ ⊢[PRAAx] realOrder (addF C F) F (addData c x) x) :
    Γ ⊢[PRAAx] realOrder C C c (fraction zero one) := by
  let N := negativeF F
  let v := negativeData x
  have hc := constant_regular (Γ := Γ) c
  have hn := negative_fast F x hf
  have comb := add_order (addF C F) F N N (addData c x) x v v h (order_refl _ _ hn)
  have left := GaussianNamedDifference.add_sub_cancel_right C F c x hc hf
  have right := cross_trans _ _ _ _ _ _ (add_negative F x hf) (zero_constant x)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left) right comb

theorem strictly_ordered_of_margin (F H : PR 2) (c x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hp : Γ ⊢[PRAAx] neg (realOrder C C c (fraction zero one)))
    (h : Γ ⊢[PRAAx] realOrder (addF C F) H (addData c x) y) :
    Γ ⊢[PRAAx] neg (realOrder H F y x) := by
  refine .impI ?_
  exact hp.wk.impE (cancel_order F c x hf.wk (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ h.wk Prf.hyp0))

theorem gap_positive (a d : PTm n) (h : Γ ⊢[PRAAx] lt a d) : Γ ⊢[PRAAx] le one (gap a d) := by
  have hgap := GaussianEulerUnitLogarithmicMargin.gap_positive a d h
  exact le_congr (.eqRefl _) (gap_square a d (le_of_lt h)).eqSymm (positive_product _ _ hgap hgap)

theorem margin_positive (a d : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] lt a d) : Γ ⊢[PRAAx] neg (realOrder C C (margin a d) (fraction zero one)) := by
  have hp := gap_positive a d h
  exact GaussianStirlingMultiplicativeBoundsCaps.strict_fractions zero one (gap a d) (large a d) (le_refl one)
    (margin_source a d ha hd).andE₁ (lt_congr (by ipra_ring) (by ipra_ring) hp)

def strict (a d b r s : PTm n) : Fm PTm n :=
  realOrder G (addF G G) (nativeCenterData a d b r (succ s)) (nativeWeightedData a d b r (succ s)) ⋏
  neg (realOrder (addF G G) G (nativeWeightedData a d b r (succ s)) (nativeCenterData a d b r (succ s)))

theorem strict_order (a d b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] lt a d) : Γ ⊢[PRAAx] strict a d b r s := by
  let z := barycenter a d r (succ s)
  let w := weight r (succ s)
  have hD := le_trans ha (le_of_lt hd)
  have hz := GaussianGammaEulerRationalLogConvexity.center_positive a d r (succ s) ha
  have hw := GaussianGammaEulerRationalLogConvexity.center_denominator_positive b r (succ s) hb
  have hC := scaled_regular w (logGammaData z (w*b)) (log_gamma_regular z (w*b) (.andI hz hw))
  exact .andI (weighted_convexity a d b r (succ s) ha hD hb)
    (strictly_ordered_of_margin G (addF G G) (margin a d) (nativeCenterData a d b r (succ s))
      (nativeWeightedData a d b r (succ s)) hC (margin_positive a d ha hD hd)
      (GaussianGammaNativeWeightedLogGap.weighted_order a d b r s ha hD hb))

theorem actual_positive_rational_log_Gamma_strict_convexity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 0) ⋏ (le one (var 2) ⋏ lt (var 0) (var 1))) ⟶ strict (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (strict_order _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNativeStrictLogConvexity
