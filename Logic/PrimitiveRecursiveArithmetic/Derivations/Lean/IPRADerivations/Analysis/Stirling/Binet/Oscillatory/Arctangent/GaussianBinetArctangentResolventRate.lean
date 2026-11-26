import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentResolvent
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower
import IPRADerivations.Analysis.Trigonometry.Hyperbolic.GaussianSineProductImaginaryLogDerivativeTail

/-!
# Uniform compact bounds for the actual arctangent integrand

At a signed rational parameter with real part (X/D>0), the original
resolvent has norm at most (D/X) and time Lipschitz constant (D²/X²).
The constants hold before passing to any quadrature limit.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentResolventRate

open_ipra
open ComplexLogarithmRemainder (eval_re_code eval_im_code normSq normSq_neg normSq_scale normSq_one)
open GaussianBinetArctangentResolvent (pole signedTimeNumerator value average pole_as_sum pole_lower reciprocal_average)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianLogGammaEulerHead (argument)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical positive_product
  qadd qmul qmul_canonical qmul_represents canonical_unique represents_congr)
open GaussianRationalLowerBounds (inverse_bound name_lower)
open GaussianRationalMetric (bounded bounded_iff distanceBounded qsub qsub_canonical)
open GaussianRationalReciprocal (reciprocal bound_congr bounded_sum bounded_product)
open GaussianRationalSyntheticDivision (qsub_congr qadd_congr qzero_add)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRootAlgebra (equal_of_values re_mul im_mul re_neg im_neg re_scale im_scale re_one im_one)
open GaussianSineProductImaginaryLogDerivative (axisNumerator)
open GaussianSineProductImaginaryLogDerivativeTail (axis_norm)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def rotation (s : Bool) : PTm n := ofGaussian (signedTimeNumerator s one) one

private theorem rotation_bound (s : Bool) : Γ ⊢[PRAAx] bounded (rotation s : PTm n) one one := by
  have h : Γ ⊢[PRAAx] normSq (signedTimeNumerator s (one : PTm n)) ≐ one*one := by
    cases s
    · exact axis_norm one
    · exact (normSq_neg (axisNumerator one)).eqTrans (axis_norm one)
  apply (bounded_iff _ _ _ _ _ (le_refl one) (le_refl one) (ofGaussian_represents _ _ (le_refl one))).iffMpr
  exact le_congr (congrMul (.eqRefl (one*one)) h.eqSymm) (.eqRefl _) (le_refl _)

private theorem rotate (s : Bool) (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (rotation s) (fraction A B) ≐ ofGaussian (signedTimeNumerator s A) B := by
  let u := signedTimeNumerator s (one : PTm n)
  let v := ComplexLogarithmRemainder.scale A ComplexLogarithmRemainder.oneCode
  have left := qmul_represents _ _ _ _ _ _ (le_refl one) hB
    (ofGaussian_represents (Γ := Γ) u one (le_refl one)) (ofGaussian_represents v B hB)
  have right := ofGaussian_represents (Γ := Γ) (signedTimeNumerator s A) B hB
  apply canonical_unique _ _ _ B (qmul_canonical _ _) (ofGaussian_canonical _ _ hB) hB (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := one_mul B) (h := left)
  cases s <;> dsimp only [u,v] <;> apply equal_of_values <;>
    simp [signedTimeNumerator,axisNumerator,re_mul,im_mul,re_neg,im_neg,re_scale,im_scale,re_one,im_one,
      eval_re_code,eval_im_code,ZT.toZ_ofNat]

theorem pole_distance (s : Bool) (X Y D sign A B a b E H : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b)
    (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] distanceBounded (fraction A B) (fraction a b) E H) :
    Γ ⊢[PRAAx] distanceBounded (pole s X Y D sign A B) (pole s X Y D sign a b) E H := by
  let z := argument X Y D sign
  let u := ofGaussian (signedTimeNumerator s A) B
  let v := ofGaussian (signedTimeNumerator s a) b
  have rotated := distance_congr (rotate s A B hB) (rotate s a b hb) (.eqRefl _) (.eqRefl _)
    (GaussianRationalRoundedPower.multiply_distance_bound (rotation s) _ _ E H hH (rotation_bound s) h)
  have displacement := (qsub_congr (pole_as_sum s X Y D sign A B hD hB).eqSymm
    (pole_as_sum s X Y D sign a b hD hb).eqSymm).eqTrans ((GaussianNameArithmetic.sum_difference z z u v).eqTrans
      ((qadd_congr (GaussianCoefficientNormOrder.qsub_self z) (.eqRefl _)).eqTrans (qzero_add _ (qsub_canonical _ _))))
  exact bound_congr displacement.eqSymm (.eqRefl _) (.eqRefl _) rotated

theorem reciprocal_distance (s : Bool) (X Y D sign A B a b E H : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b)
    (hH : Γ ⊢[PRAAx] le one H) (h : Γ ⊢[PRAAx] distanceBounded (fraction A B) (fraction a b) E H) :
    Γ ⊢[PRAAx] distanceBounded (reciprocal (pole s X Y D sign A B)) (reciprocal (pole s X Y D sign a b))
      (D*D*E) (X*X*H) := by
  let p := pole s X Y D sign A B
  let q := pole s X Y D sign a b
  have hX := hz.andE₁.andE₁
  have hD := hz.andE₂
  have hp := pole_lower s X Y D sign A B hD hB
  have hq := pole_lower s X Y D sign a b hD hb
  have np := GaussianNameReciprocal.lower_norm_positive p D hD (name_lower p X D hX hD hp)
  have nq := GaussianNameReciprocal.lower_norm_positive q D hD (name_lower q X D hX hD hq)
  have dpq := distance_symmetric _ _ _ _ hH (pole_distance s X Y D sign A B a b E H hD hB hb hH h)
  have b₁ := bounded_product (reciprocal p) (qsub q p) D X E H hX hH
    (inverse_bound p X D hX hD hp) dpq
  have b₂ := bounded_product (qmul (reciprocal p) (qsub q p)) (reciprocal q) (D*E) (X*H) D X
    (positive_product _ _ hX hH) hX b₁ (inverse_bound q X D hX hD hq)
  exact bound_congr (GaussianNameReciprocal.inverse_difference p q np nq).eqSymm (by ipra_ring) (by ipra_ring) b₂

private theorem half_bound : Γ ⊢[PRAAx] bounded (fraction one two : PTm n) one two := by
  let a := (ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode : PTm n)
  have ht := le_succ_self (Γ := Γ) one
  have e : Γ ⊢[PRAAx] normSq a ≐ one*one :=
    (normSq_scale _ _).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
  exact (bounded_iff _ _ _ _ _ ht ht (ofGaussian_represents a two ht)).iffMpr
    (le_congr (congrMul (.eqRefl (two*two)) e.eqSymm) (by ipra_ring) (le_refl ((two*two)*(one*one))))

theorem uniform_bound (X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (value X Y D sign A B) D X := by
  let p := pole false X Y D sign A B
  let m := pole true X Y D sign A B
  have hX := hz.andE₁.andE₁
  have hD := hz.andE₂
  have hx := positive_product _ _ hX hX
  have ht := le_succ_self (Γ := Γ) one
  have s := bounded_sum (reciprocal p) (reciprocal m) D X D X hX hX
    (inverse_bound _ _ _ hX hD (pole_lower false X Y D sign A B hD hB))
    (inverse_bound _ _ _ hX hD (pole_lower true X Y D sign A B hD hB))
  have b := bounded_product (fraction one two) _ one two _ _ ht hx half_bound s
  have pad := bounded_radius_mono _ _ _ D X (positive_product _ _ ht hx) hX
    (le_of_eq_add (d := zero) (by ipra_ring)) b
  exact bound_congr (reciprocal_average X Y D sign A B hz hB).eqSymm (.eqRefl _) (.eqRefl _) pad

theorem time_distance (X Y D sign A B a b E H : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b) (hH : Γ ⊢[PRAAx] le one H)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction A B) (fraction a b) E H) :
    Γ ⊢[PRAAx] distanceBounded (value X Y D sign A B) (value X Y D sign a b) (D*D*E) (X*X*H) := by
  let N := D*D*E
  let M := X*X*H
  have hX := hz.andE₁.andE₁
  have hx : Γ ⊢[PRAAx] le one M := positive_product _ _ (positive_product _ _ hX hX) hH
  have ht := le_succ_self (Γ := Γ) one
  have pos := reciprocal_distance false X Y D sign A B a b E H hz hB hb hH h
  have neg := reciprocal_distance true X Y D sign A B a b E H hz hB hb hH h
  have summ := GaussianNameArithmetic.sum_distance _ _ _ _ N N M hx pos neg
  have raw := bounded_product (fraction one two) _ one two (N+N) M ht hx half_bound summ
  have prod := bound_congr (GaussianRationalRoundedPower.multiplication_difference (fraction one two) _ _).eqSymm
    (one_mul _) (.eqRefl _) raw
  have rad := distance_radius_mono _ _ _ _ N M (positive_product _ _ ht hx) hx
    (le_of_eq_add (d := zero) (by ipra_ring)) prod
  exact distance_congr (reciprocal_average X Y D sign A B hz hB).eqSymm
    (reciprocal_average X Y D sign a b hz hb).eqSymm (.eqRefl _) (.eqRefl _) rad

theorem actual_Binet_arctangent_resolvent_uniform_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 0) (var 2) (var 3) ⋏ le one (var 5)) ⟶
      bounded (value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (var 0)) :=
  closeUniv 6 (.impI (uniform_bound _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentResolventRate
