import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetReciprocalRows
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.Trigonometry.Hyperbolic.ProductEstimates.GaussianSineProductImaginaryLogDerivative

/-!
# The two actual right-half-plane resolvents for Binet's arctangent

At every rational integration coordinate (u), both (z+iu) and
(z-iu) retain the positive real margin of (z). Their original
rational reciprocals give the literal normalized identity
`z/(z²+u²) = ((z+iu)⁻¹+(z−iu)⁻¹)/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentResolvent

open_ipra
open ComplexLogarithmRemainder (code scale oneCode normSq normSq_code eval_re_code eval_im_code)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents qadd qmul
  qadd_represents qmul_represents qadd_canonical qmul_canonical positive_product canonical_unique represents_congr)
open GaussianRationalLowerBounds (lower lower_from_representation lower_congr product_lower name_lower)
open GaussianRationalReciprocal (reciprocal reciprocal_identity)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr rescale_to)
open GaussianReciprocalHorner (qmul_associative qmul_one_right qadd_commutative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open GaussianRootAlgebra (equal_of_values re_add im_add re_mul im_mul re_neg im_neg re_scale im_scale re_one im_one)
open GaussianSineProductImaginaryLogDerivative (axisNumerator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def signedTimeNumerator (s : Bool) (A : PTm n) : PTm n :=
  if s then ComplexLogarithmRemainder.neg (axisNumerator A) else axisNumerator A
def poleNumerator (s : Bool) (X Y D sign A B : PTm n) : PTm n :=
  ComplexLogarithmRemainder.add (scale B (native X Y sign)) (scale D (signedTimeNumerator s A))
def pole (s : Bool) (X Y D sign A B : PTm n) : PTm n := ofGaussian (poleNumerator s X Y D sign A B) (D*B)
def polynomial (X Y D sign A B : PTm n) : PTm n :=
  qadd (qmul (argument X Y D sign) (argument X Y D sign)) (qmul (fraction A B) (fraction A B))
def value (X Y D sign A B : PTm n) : PTm n :=
  qmul (argument X Y D sign) (reciprocal (polynomial X Y D sign A B))
def average (X Y D sign A B : PTm n) : PTm n :=
  qmul (fraction one two) (qadd (reciprocal (pole false X Y D sign A B)) (reciprocal (pole true X Y D sign A B)))

@[simp] theorem subst_signedTimeNumerator {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (A : PTm n) :
    Syn.subst σ (signedTimeNumerator s A) = signedTimeNumerator s (Syn.subst σ A) := by
  cases s <;> simp [signedTimeNumerator]

@[simp] theorem subst_pole {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (X Y D sign A B : PTm n) :
    Syn.subst σ (pole s X Y D sign A B) = pole s (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D)
      (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B) := by simp [pole,poleNumerator]

ipra_subst value [polynomial]

theorem pole_as_sum (s : Bool) (X Y D sign A B : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (argument X Y D sign) (ofGaussian (signedTimeNumerator s A) B) ≐ pole s X Y D sign A B := by
  let z := native X Y sign
  let u := signedTimeNumerator s A
  have hd := positive_product D B hD hB
  have zz := rescale_to (argument X Y D sign) z D B (D*B) (ofGaussian_represents (Γ := Γ) z D hD) (.eqRefl _)
  have uu := rescale_to (ofGaussian u B) u B D (D*B) (ofGaussian_represents u B hB) (mul_comm _ _)
  exact canonical_unique _ _ _ (D*B) (qadd_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (qadd_represents _ _ _ _ _ hd zz uu) (ofGaussian_represents _ _ hd)

private theorem real_norm (s : Bool) (X Y D sign A B : PTm n) : Γ ⊢[PRAAx]
    le ((X*B)*(X*B)) (normSq (poleNumerator s X Y D sign A B)) := by
  let u := poleNumerator s X Y D sign A B
  apply le_of_eq_add (d := normSq (code (ZT.ofNat zero) (ComplexLogarithmRemainder.im u)))
  cases s <;> apply deriveNat <;> ipra_simps <;>
    simp [ComplexLogarithmRemainder.normSq_eval,u,poleNumerator,signedTimeNumerator,native,axisNumerator,
      re_add,im_add,re_neg,im_neg,re_scale,im_scale,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;> ring

theorem pole_lower (s : Bool) (X Y D sign A B : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (pole s X Y D sign A B) X D := by
  let P := poleNumerator s X Y D sign A B
  have h := positive_product D B hD hB
  have bound : Γ ⊢[PRAAx] le ((X*B)*(X*B)*(D*D)) (normSq P*(D*D)) :=
    mul_le_mul_right (D*D) (real_norm s X Y D sign A B)
  apply lower_from_representation _ P (D*B) X D h hD (ofGaussian_represents _ _ h)
  exact le_congr (by ipra_ring) (by ipra_ring) bound

theorem product_polynomial (X Y D sign A B : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (pole false X Y D sign A B) (pole true X Y D sign A B) ≐ polynomial X Y D sign A B := by
  let Z := native X Y sign
  let U := scale A oneCode
  let z := argument X Y D sign
  let u := fraction A B
  let E := D*B
  have hd := positive_product D B hD hB
  have h := positive_product E E hd hd
  have zz := rescale_to z Z D B E (ofGaussian_represents (Γ := Γ) Z D hD) (.eqRefl _)
  have uu := rescale_to u U B D E (ofGaussian_represents U B hB) (mul_comm _ _)
  have left := qmul_represents _ _ _ _ _ _ hd hd (ofGaussian_represents (poleNumerator false X Y D sign A B) E hd)
    (ofGaussian_represents (poleNumerator true X Y D sign A B) E hd)
  have right := qadd_represents _ _ _ _ _ h (qmul_represents _ _ _ _ _ _ hd hd zz zz) (qmul_represents _ _ _ _ _ _ hd hd uu uu)
  apply canonical_unique _ _ _ (E*E) (qmul_canonical _ _) (qadd_canonical _ _) h (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  dsimp only [Z,U]
  apply equal_of_values <;> simp [poleNumerator,signedTimeNumerator,axisNumerator,re_add,im_add,re_mul,im_mul,
    re_neg,im_neg,re_scale,im_scale,re_one,im_one,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;> ring

theorem polynomial_lower (X Y D sign A B : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (polynomial X Y D sign A B) (X*X) (D*D) :=
  lower_congr (product_polynomial X Y D sign A B hD hB) (.eqRefl _) (.eqRefl _)
    (product_lower _ _ _ _ _ _ hD hD (pole_lower false X Y D sign A B hD hB) (pole_lower true X Y D sign A B hD hB))

private theorem half_sum (X Y D sign A B : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (fraction one two) (qadd (pole false X Y D sign A B) (pole true X Y D sign A B)) ≐
      argument X Y D sign := by
  let Z := native X Y sign
  let E := D*B
  have hd := positive_product D B hD hB
  have h₂ := le_succ_self (Γ := Γ) one
  have hh := positive_product two E h₂ hd
  have mom := qadd_represents _ _ _ _ _ hd (ofGaussian_represents (Γ := Γ) (poleNumerator false X Y D sign A B) E hd)
    (ofGaussian_represents (poleNumerator true X Y D sign A B) E hd)
  have left := qmul_represents _ _ _ _ _ _ h₂ hd (ofGaussian_represents (scale one oneCode) two h₂) mom
  have right := rescale_to (argument X Y D sign) Z D (two*B) (two*E) (ofGaussian_represents _ _ hD)
    (by dsimp only [E]; ipra_ring)
  apply canonical_unique _ _ _ (two*E) (qmul_canonical _ _) (ofGaussian_canonical _ _ hD) hh (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  dsimp only [Z]
  apply equal_of_values <;> simp [poleNumerator,signedTimeNumerator,axisNumerator,re_add,im_add,re_mul,im_mul,
    re_neg,im_neg,re_scale,im_scale,re_one,im_one,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;> ring

private theorem average_cleared (p m h : PTm n) (hp : Γ ⊢[PRAAx] qmul p (reciprocal p) ≐ qone)
    (hm : Γ ⊢[PRAAx] qmul m (reciprocal m) ≐ qone)
    (pc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical p) (mc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical m) : Γ ⊢[PRAAx]
    qmul (qmul p m) (qmul h (qadd (reciprocal p) (reciprocal m))) ≐ qmul h (qadd p m) := by
  let W := qmul p m
  let v := qadd (reciprocal p) (reciprocal m)
  have commute := (qmul_associative (Γ := Γ) W h v).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative W h) (.eqRefl _)).eqTrans (qmul_associative h W v))
  have left := (qmul_congr (qmul_commutative p m) (.eqRefl (reciprocal p))).eqTrans
    ((qmul_associative m p (reciprocal p)).eqTrans
      ((qmul_congr (.eqRefl _) hp).eqTrans (qmul_one_right m mc)))
  have right := (qmul_associative p m (reciprocal m)).eqTrans
    ((qmul_congr (.eqRefl _) hm).eqTrans (qmul_one_right p pc))
  exact commute.eqTrans (qmul_congr (.eqRefl _) ((qmul_add W (reciprocal p) (reciprocal m)).eqTrans
    ((qadd_congr left right).eqTrans (qadd_commutative m p))))

theorem reciprocal_average (X Y D sign A B : PTm n) (h : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] value X Y D sign A B ≐ average X Y D sign A B := by
  let p := pole false X Y D sign A B
  let m := pole true X Y D sign A B
  let W := qmul p m
  let Q := polynomial X Y D sign A B
  let V := average X Y D sign A B
  let z := argument X Y D sign
  have hX := h.andE₁.andE₁
  have hD := h.andE₂
  have hd := positive_product D B hD hB
  have lp := name_lower p X D hX hD (pole_lower false X Y D sign A B hD hB)
  have lm := name_lower m X D hX hD (pole_lower true X Y D sign A B hD hB)
  have hQ := polynomial_lower X Y D sign A B hD hB
  have D₂ := positive_product D D hD hD
  have lq := name_lower Q (X*X) (D*D) (positive_product X X hX hX) D₂ hQ
  have invp := reciprocal_identity p (GaussianNameReciprocal.lower_norm_positive p D hD lp)
  have invm := reciprocal_identity m (GaussianNameReciprocal.lower_norm_positive m D hD lm)
  have invq := reciprocal_identity Q (GaussianNameReciprocal.lower_norm_positive Q (D*D) D₂ lq)
  have cleared : Γ ⊢[PRAAx] qmul V Q ≐ z :=
    (qmul_congr (.eqRefl V) (product_polynomial X Y D sign A B hD hB).eqSymm).eqTrans
      ((qmul_commutative V W).eqTrans
        ((average_cleared p m (fraction one two) invp invm (ofGaussian_canonical _ _ hd) (ofGaussian_canonical _ _ hd)).eqTrans
          (half_sum X Y D sign A B hD hB)))
  exact ((qmul_one_right V (qmul_canonical _ _)).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) invq.eqSymm).eqTrans ((qmul_associative V Q (reciprocal Q)).eqSymm.eqTrans
      (qmul_congr cleared (.eqRefl _))))).eqSymm

theorem actual_Binet_arctangent_resolvent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 0) (var 2) (var 3) ⋏ le one (var 5)) ⟶
      value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
        average (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (reciprocal_average _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentResolvent
