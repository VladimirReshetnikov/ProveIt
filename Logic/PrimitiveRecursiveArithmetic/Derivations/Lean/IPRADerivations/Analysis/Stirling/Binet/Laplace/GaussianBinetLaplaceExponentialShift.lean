import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceExponential
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadraturePrecision
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualRadius
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift

/-!
# The actual Laplace exponential at a unit shift

For the original signed rational parameter and a rational integration
time, the original names satisfy `exp(-(z+1)t) = exp(-zt) exp(-t)`.
The factor on the right is the actual separately computed decay name.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceExponentialShift

open_ipra
open ComplexLogarithmRemainder (code neg mul scale oneCode eval_re_code eval_im_code normSq)
open GaussianBinetLaplaceExponential (exponent nameF data exponent_bound)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source native)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian_represents positive_product qadd qmul qadd_canonical qmul_canonical
  qadd_represents qmul_represents canonical_unique represents_congr)
open GaussianRationalMetric (qnegative qnegative_represents bounded)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRootAlgebra (equal_of_values re_add im_add re_neg im_neg re_mul im_mul re_scale im_scale re_one im_one)
open GaussianSignedNameExponentialOrder (constant_input)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem shifted_source (X Y D sign R : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R) :
    Γ ⊢[PRAAx] source (X+D) Y D sign (R+one) := by
  have hs := h.andE₁.andE₁.andE₂
  have hb : Γ ⊢[PRAAx] le (X*X+Y*Y) ((R*D)*(R*D)) :=
    le_congr (native_norm X Y sign hs) (.eqRefl _) h.andE₂
  have hX : Γ ⊢[PRAAx] le X (R*D) :=
    LeanProofs.IPRA.DiophantineNumberTheory.Coprime.le_of_sq_le (le_trans (le_add_right _ _) hb)
  apply Prf.andI
  · exact .andI (.andI (le_trans h.andE₁.andE₁.andE₁ (le_add_right _ _)) hs) h.andE₁.andE₂
  · apply le_congr (native_norm (X+D) Y sign hs).eqSymm (.eqRefl _)
    ipra_le sl hb+2*𝔞 D*sl hX

theorem shifted_exponent (X Y D sign A B : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (exponent X Y D sign A B) (decayPoint A B) ≐ exponent (X+D) Y D sign A B := by
  let z := native X Y sign
  let w := native (X+D) Y sign
  let t := scale A oneCode
  let b := fraction A B
  have hd := positive_product _ _ hD hB
  have hT := ofGaussian_represents (Γ := Γ) t B hB
  have hN := qnegative_represents b t B hT
  have base := qmul_represents _ _ _ _ _ _ hD hB
    (qnegative_represents (argument X Y D sign) z D (ofGaussian_represents _ _ hD)) hT
  have shifted := qmul_represents _ _ _ _ _ _ hD hB
    (qnegative_represents (argument (X+D) Y D sign) w D (ofGaussian_represents _ _ hD)) hT
  have decay := rescale_to (qnegative b) (ComplexLogarithmRemainder.neg t) B D (D*B) hN (mul_comm _ _)
  have sum := qadd_represents _ _ _ _ _ hd base decay
  apply canonical_unique _ _ _ (D*B) (qadd_canonical _ _) (qmul_canonical _ _) hd (hrv := shifted)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := sum)
  dsimp only [z,w,t]
  apply equal_of_values <;> simp only [re_add,im_add,re_neg,im_neg,re_mul,im_mul,re_scale,im_scale,re_one,im_one,
    native,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring

def productData (X Y D sign R T A B : PTm n) : PTm n :=
  multiplyData nameF decayF (data X Y D sign R T A B) (decayData A B)

theorem shift_multiply (X Y D sign R T A B : PTm n) (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hB : Γ ⊢[PRAAx] le one B) (ht : Γ ⊢[PRAAx] le A (T*B)) : Γ ⊢[PRAAx]
    crossEquivalent nameF (multiplyF nameF decayF) (data (X+D) Y D sign (R+one) T A B)
      (productData X Y D sign R T A B) := by
  let C := constantF
  let E := nameF
  let u := exponent X Y D sign A B
  let v := decayPoint A B
  let w := exponent (X+D) Y D sign A B
  let M := (R+one)*T+one
  let S := GaussianNameBounds.U C v
  have hM : Γ ⊢[PRAAx] le one M := le_add_left _ _
  have hu := constant_input u (R*T) (exponent_bound X Y D sign R T A B hz hB ht)
  have hw := constant_input w ((R+one)*T)
    (exponent_bound (X+D) Y D sign (R+one) T A B (shifted_source X Y D sign R hz) hB ht)
  have hv := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) C v (constant_regular v)
  have vu : Γ ⊢[PRAAx] le T M := by dsimp only [M]; ipra_le 𝔞 R*𝔞 T+1
  have vb := GaussianRationalReciprocal.bounded_negative _ _ _ (le_refl one)
    (GaussianEulerExponentCompactBounds.fraction_bound A B T hB ht)
  have pad : Γ ⊢[PRAAx] le (T*one) (M*one) := le_congr (by ipra_ring) (by ipra_ring) vu
  have vv := constant_input v M (bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) pad vb)
  have uu := GaussianExponentialRadiusIndependence.input_widen C (R*T) M u hu
    (by dsimp only [M]; ipra_le 𝔞 T+1)
  have p₁ := GaussianExponentialRadiusIndependence.same_input_cross C (R*T) M u hu uu
  have p₂ := GaussianExponentialRadiusIndependence.same_input_cross C S M v hv vv
  have obs (R x : PTm n) (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input C R x) :=
    GaussianRadiusExponentialName.name_regular C R x h
  have replace := multiply_cross E E decayF E (data X Y D sign R T A B)
    (GaussianRadiusExponentialName.data M u) (decayData A B) (GaussianRadiusExponentialName.data M v)
    (obs _ _ hu) (obs _ _ uu) (obs _ _ hv) (obs _ _ vv) p₁ p₂
  have add := GaussianExponentialAddition.exponential_add_cross C C M u v hM uu vv
  have sumInput := GaussianExponentialReference.add_input C C M u v uu vv
  have point := GaussianNamedGammaHalfShift.constant_sum u v w (shifted_exponent X Y D sign A B hz.andE₁.andE₂ hB)
  have final := GaussianExponentialRadiusIndependence.independent_radii_proper (addF C C) C (M+M) ((R+one)*T)
    (addData u v) w sumInput hw point
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ add final))

theorem actual_Binet_Laplace_exponential_unit_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let X := var 0
     let Y := var 1
     let D := var 2
     let sign := var 3
     let R := var 4
     let T := var 5
     let A := var 6
     let B := var 7
     (source X Y D sign R ⋏ (le one B ⋏ le A (T*B))) ⟶
       crossEquivalent nameF (multiplyF nameF decayF) (data (X+D) Y D sign (R+one) T A B)
         (productData X Y D sign R T A B)) :=
  closeUniv 8 (.impI (shift_multiply _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceExponentialShift
