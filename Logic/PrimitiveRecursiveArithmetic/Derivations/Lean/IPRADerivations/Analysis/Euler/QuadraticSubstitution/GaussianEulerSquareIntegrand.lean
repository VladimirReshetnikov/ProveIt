import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerSquareKernel
import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingCancellation
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureSquareJacobian

/-!
# The original Euler integrand under the quadratic substitution

For positive rational u and α, the Jacobian-weighted original Euler
integrand at αu² is twice the original scale power α^(z/B) times
u^(2z/B-1) exp(-αu²). The original evaluator and the finite quadrature
Jacobian evaluator agree at the actual product query.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareIntegrand

open_ipra
open GaussianEulerIntegrandName (nameF data powerF powerData power_regular evaluatorF fixedData)
open GaussianEulerSquareKernel (doubled kernelF kernelData kernel_regular factoredF factoredData weightedF weightedData)
open GaussianEulerPositiveScalingIntegrand (source)
open GaussianEulerPositiveScalingConstant (scaleF scaleData)
open GaussianRationalQuadratureSquareCells (jacobian timeMap)
open GaussianRationalQuadratureDilation (pullData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl cross_at)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def jacobianValue (a b c d : PTm n) : PTm n := fraction (two*c*a) (d*b)
def jacobianData (z B a b c d : PTm n) : PTm n :=
  multiplyData constantF nameF (jacobianValue a b c d) (data z B (c*(a*a)) (d*(b*b)))
abbrev jacobianF : PR 2 := multiplyF constantF nameF
abbrev factorF : PR 2 := multiplyF constantF scaleF
def factorData (z B c d : PTm n) : PTm n := multiplyData constantF scaleF (fraction two one) (scaleData z B c d)
abbrev factoredKernelF : PR 2 := multiplyF factorF kernelF
def factoredKernelData (z B a b c d : PTm n) : PTm n :=
  multiplyData factorF kernelF (factorData z B c d) (kernelData (doubled z B) B a b c d)
def query (p z B a b c d : PTm n) : PTm n :=
  GaussianFastValueCut.exponent
    (multiplyModulus constantF nameF (jacobianValue a b c d) (data z B (c*(a*a)) (d*(b*b)))) p

private theorem commute_left (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (multiplyF g h)) (multiplyF g (multiplyF f h))
      (multiplyData f (multiplyF g h) x (multiplyData g h y z))
      (multiplyData g (multiplyF f h) y (multiplyData f h x z)) := by
  have permute := multiply_cross (multiplyF f g) (multiplyF g f) h h
    (multiplyData f g x y) (multiplyData g f y x) z z (multiply_fast _ _ _ _ hf hg)
    (multiply_fast _ _ _ _ hg hf) hh hh (multiply_commutative f g x y hf hg) (cross_refl _ _ hh)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative f g h x y z hf hg hh))
    (cross_trans _ _ _ _ _ _ permute (multiply_associative g f h y x z hg hf hh))

private theorem double_scale (z B c d : PTm n) (h : Γ ⊢[PRAAx] le one B ⋏ (le one c ⋏ le one d)) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF powerF) factorF
      (multiplyData constantF powerF (fraction (two*c) d) (powerData z B c d)) (factorData z B c d) := by
  let t : PTm n := fraction two one
  let α := fraction c d
  let w := fraction (two*c) d
  let v := powerData z B c d
  have fractions : Γ ⊢[PRAAx] GaussianRationalHorner.qmul t α ≐ w :=
    (GaussianEulerDampedTimeRate.fraction_product two one c d (le_refl one) h.andE₂.andE₂).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul d))
  have ht := constant_regular (Γ := Γ) t
  have ha := constant_regular (Γ := Γ) α
  have hv := power_regular z B c d h
  have prod := cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross t α)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ fractions)
  have step := multiply_cross constantF (multiplyF constantF constantF) powerF powerF w
    (multiplyData constantF constantF t α) v v (constant_regular w) (multiply_fast _ _ _ _ ht ha) hv hv
    (cross_symm _ _ _ _ prod) (cross_refl _ _ hv)
  exact cross_trans _ _ _ _ _ _ step (multiply_associative constantF constantF powerF t α v ht ha hv)

theorem original_quadratic_integrand (z B a b c d : PTm n) (h : Γ ⊢[PRAAx] source B a b c d) :
    Γ ⊢[PRAAx] crossEquivalent jacobianF factoredKernelF
      (jacobianData z B a b c d) (factoredKernelData z B a b c d) := by
  let w := fraction (two*c) d
  let t := fraction a b
  let v := powerData z B c d
  let k := kernelData (GaussianEulerSquarePower.doubledMinusOne z B) B a b c d
  let e := data z B (c*(a*a)) (d*(b*b))
  let j := jacobianValue a b c d
  let wv := multiplyData constantF powerF w v
  let tk := weightedData z B a b c d
  have hc : Γ ⊢[PRAAx] GaussianEulerPositiveScalingConstant.source B c d := .andI h.andE₁ h.andE₂.andE₁
  have hw := constant_regular (Γ := Γ) w
  have ht := constant_regular (Γ := Γ) t
  have hv := power_regular z B c d hc
  have hk := kernel_regular (GaussianEulerSquarePower.doubledMinusOne z B) B a b c d h
  have he := GaussianEulerIntegrandName.name_regular z B (c*(a*a)) (d*(b*b))
    (GaussianEulerPositiveScalingIntegrand.scaled_source z B (a*a) (b*b) c d
      (GaussianEulerSquareKernel.square_source B a b c d h))
  have htk := multiply_fast constantF kernelF t k ht hk
  have rawJacobian :
      Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF constantF) constantF
        (multiplyData constantF constantF w t) j :=
    cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross w t)
      (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
        (GaussianEulerDampedTimeRate.fraction_product (two*c) d a b hc.andE₂.andE₂ h.andE₂.andE₂.andE₂))
  have start := multiply_cross constantF (multiplyF constantF constantF) nameF factoredF j
    (multiplyData constantF constantF w t) e (factoredData z B a b c d)
    (constant_regular j) (multiply_fast _ _ _ _ hw ht) he (multiply_fast powerF kernelF v k hv hk)
    (cross_symm _ _ _ _ rawJacobian) (GaussianEulerSquareKernel.original_square_scaling z B a b c d h)
  have reassociate := multiply_associative constantF constantF factoredF w t
    (factoredData z B a b c d) hw ht (multiply_fast powerF kernelF v k hv hk)
  have permute := multiply_cross constantF constantF (multiplyF constantF factoredF) (multiplyF powerF weightedF)
    w w (multiplyData constantF factoredF t (factoredData z B a b c d))
    (multiplyData powerF weightedF v tk) hw hw
    (multiply_fast constantF factoredF t _ ht (multiply_fast powerF kernelF v k hv hk))
    (multiply_fast powerF weightedF v tk hv htk) (cross_refl _ _ hw) (commute_left constantF powerF kernelF t v k ht hv hk)
  have grouped := multiply_associative constantF powerF weightedF w v tk hw hv htk
  have hfactor := multiply_fast constantF scaleF (fraction two one) (scaleData z B c d)
    (constant_regular _) (GaussianEulerPositiveScalingCancellation.scale_regular z B c d hc)
  have finish := multiply_cross (multiplyF constantF powerF) factorF weightedF kernelF
    wv (factorData z B c d) tk (kernelData (doubled z B) B a b c d)
    (multiply_fast constantF powerF w v hw hv) hfactor htk (kernel_regular (doubled z B) B a b c d h)
    (double_scale z B c d hc) (GaussianEulerSquareKernel.original_weighted_kernel z B a b c d h)
  exact cross_trans _ _ _ _ _ _ start (cross_trans _ _ _ _ _ _ reassociate
    (cross_trans _ _ _ _ _ _ permute (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ grouped) finish)))

theorem jacobian_sample (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    ap2 jacobianF p (jacobianData z B a b c d) ≐
      ap3 (GaussianRationalQuadratureSquareJacobian.jacobianF evaluatorF) (query p z B a b c d)
        (pairT a b) (pullData c d (fixedData z B)) := by
  let k := query p z B a b c d
  have jt : Γ ⊢[PRAAx] jacobian c d (pairT a b) ≐ jacobianValue a b c d :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (congrMul (.eqRefl _) (fst_pair a b))
      (congrMul (.eqRefl _) (snd_pair a b))
  have et : Γ ⊢[PRAAx] timeMap c d (pairT a b) ≐ pairT (c*(a*a)) (d*(b*b)) :=
    congrPairT ((congrMul (congrMul (.eqRefl _) (fst_pair a b)) (fst_pair a b)).eqTrans (by ipra_ring))
      ((congrMul (congrMul (.eqRefl _) (snd_pair a b)) (snd_pair a b)).eqTrans (by ipra_ring))
  have raw := GaussianRationalQuadratureSquareJacobian.jacobian_at (Γ := Γ) evaluatorF k (pairT a b) c d (fixedData z B)
  have sample := (congrAp3 evaluatorF (.eqRefl k) et (.eqRefl _)).eqTrans
    (GaussianEulerIntegrandName.sample_at k z B (c*(a*a)) (d*(b*b)))
  have original := (GaussianNameArithmetic.multiply_at (Γ := Γ) constantF nameF (jacobianValue a b c d)
    (data z B (c*(a*a)) (d*(b*b))) p).eqTrans
    (GaussianNameArithmetic.recode_congr
      (GaussianRationalSyntheticDivision.qmul_congr (constant_at k (jacobianValue a b c d)) (.eqRefl _)))
  exact original.eqTrans ((GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr jt sample).eqSymm.eqTrans raw.eqSymm))

theorem actual_original_quadratic_integrand_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ crossEquivalent jacobianF factoredKernelF
      (jacobianData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (factoredKernelData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_quadratic_integrand _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_quadratic_integrand_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (ap3 (GaussianRationalQuadratureSquareJacobian.jacobianF evaluatorF)
        (query (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (pairT (var 4) (var 5)) (pullData (var 6) (var 7) (fixedData (var 2) (var 3))))
        (ap2 factoredKernelF (var 1) (factoredKernelData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (GaussianRationalDistanceOrder.distance_congr (jacobian_sample _ _ _ _ _ _ _) (.eqRefl _)
    (.eqRefl _) (.eqRefl _) (cross_at _ _ _ _ _ _ (original_quadratic_integrand _ _ _ _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareIntegrand
