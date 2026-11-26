import IPRADerivations.Analysis.Trigonometry.SineProducts.Scaling.GaussianSineProductScaledArgumentIdentity
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaReflectionSineTransfer

/-!
# The undivided sine-product argument agrees with the reflection argument

The quarter-turn program and the ordinary multiplication program use
the same original π name. The factor of (i/2) in the quarter turn
cancels exactly with the encoded coefficient (-2iz/B).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductReflectionArgument

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSineProductScaledArguments (coefficient nameF data name_regular)
open GaussianArctangentQuarterExponential (quarterF)
open GaussianBoundedConstantProductName (clock)
open GaussianArctangentExponentialPrefix (halfI)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaReflectionSineTransfer (argumentF argumentData)
open GaussianNameArithmetic (multiplyModulus multiply_fast)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique
  qmul qmul_canonical qmul_represents represents_congr represents_rescale positive_product)
open GaussianRationalMetric (bounded bounded_iff distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianNamedSincSamples (common_late_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRootAlgebra (equal_of_values re_scale im_scale re_mul im_mul re_neg im_neg)
open ComplexLogarithmRemainder (scale mul eval_re_code eval_im_code)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "piF" => GaussianGammaHalfPiName.nameF

theorem reflection_coefficient (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (coefficient z B one) halfI ≐ ofGaussian z B := by
  let a := scale two (mul (ComplexLogarithmRemainder.neg imaginaryCode) z)
  have h1 := positive_product B one hB (le_refl one)
  have h2 : Γ ⊢[PRAAx] le one two := le_succ_self _
  have left := qmul_represents (coefficient z B one) halfI a imaginaryCode (B*one) two h1 h2
    (ofGaussian_represents _ _ h1) (ofGaussian_represents _ _ h2)
  have right := represents_rescale (ofGaussian z B) z B two (ofGaussian_represents _ _ hB)
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (mul a imaginaryCode) (scale two z) := by
    dsimp only [a]
    apply equal_of_values <;>
      simp only [re_mul,im_mul,re_scale,im_scale,re_neg,im_neg,imaginaryCode,
        eval_re_code,eval_im_code,ZT.toZ_ofNat] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ hB)
    (positive_product _ _ hB h2) (represents_congr (.eqRefl _) e (by ipra_ring) left) right

theorem scaled_argument_at (z R B x p : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B one x) ≐
      qmul (ofGaussian z B) (ap2 piF (clock p (two*R)) x) := by
  let t := clock p (two*R)
  have q : Γ ⊢[PRAAx] ap2 quarterF t x ≐ qmul halfI (ap2 piF t x) :=
    GaussianArctangentQuarterExponential.sample_at t x
  have rearranged : Γ ⊢[PRAAx] qmul (coefficient z B one) (ap2 quarterF t x) ≐
      qmul (ofGaussian z B) (ap2 piF t x) :=
    (qmul_congr (.eqRefl _) q).eqTrans ((qmul_associative _ _ _).eqSymm.eqTrans
      (qmul_congr (reflection_coefficient z B hB) (.eqRefl _)))
  exact (GaussianSineProductScaledArguments.sample_at z R B one x p).eqTrans rearranged

def budget (z R B x : PTm n) : PTm n :=
  R*two+(multiplyModulus piF constantF x (ofGaussian z B)+one)

@[simp] theorem subst_budget {l : ℕ} (σ : Fin n → PTm l) (z R B x : PTm n) :
    Syn.subst σ (budget z R B x) = budget (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ x) :=
  by simp [budget]

theorem diagonal_argument (z R B x p : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B one x))
      (ap2 argumentF p (argumentData z B x)) (budget z R B x) (unit p) := by
  let C := ofGaussian z B
  let t := clock p (two*R)
  have hu := unit_positive (Γ := Γ) p
  have hC : Γ ⊢[PRAAx] bounded C R one := (bounded_iff _ z B R one hB (le_refl _) (ofGaussian_represents _ _ hB)).iffMpr
    (le_congr (by ipra_ring) (by ipra_ring) hz)
  have reg := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have gap := common_late_distance piF x p t p reg (le_add_right _ _) (le_refl p)
  have left := distance_congr (scaled_argument_at z R B x p hB).eqSymm
    (qmul_commutative C (ap2 piF p x)) (.eqRefl _) (.eqRefl _)
    (multiply_distance C _ _ R two (unit p) hu hC gap)
  have right := distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at p C)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error piF constantF x C p reg (constant_regular C))
  exact distance_triangle_same _ _ _ _ _ _ hu left (distance_symmetric _ _ _ _ hu right)

theorem reflection_argument_cross (z R B x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent nameF argumentF (data z R B one x) (argumentData z B x) := by
  apply cross_of_diagonal_rate _ _ _ _ (budget z R B x)
    (name_regular z R B one x hB (le_refl one) hz)
    (multiply_fast piF constantF x (ofGaussian z B) (GaussianGammaHalfPiName.name_regular x) (constant_regular _))
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have b : Δ ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hB.shift
  have h : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sh z) (sh R*sh B) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using hz.shift
  have left : sh (data z R B one x) = data (sh z) (sh R) (sh B) one (sh x) := by
    simp only [sh,Syn.shift,GaussianSineProductScaledArguments.subst_data,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
  have right : sh (argumentData z B x) = argumentData (sh z) (sh B) (sh x) := by
    simp [sh,Syn.shift,argumentData]
  have cost : sh (budget z R B x) = budget (sh z) (sh R) (sh B) (sh x) := by simp [sh,Syn.shift]
  change Δ ⊢[PRAAx] distanceBounded (ap2 nameF (var 0) (sh (data z R B one x)))
    (ap2 argumentF (var 0) (sh (argumentData z B x))) (sh (budget z R B x)) (unit (var 0))
  rw [left,right,cost]
  exact diagonal_argument (sh z) (sh R) (sh B) (sh x) (var 0) b h

theorem actual_sine_product_reflection_argument_cross_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ ComplexLogarithmRemainder.bounded (var 3) (var 2*var 1) ⟶
      crossEquivalent nameF argumentF (data (var 3) (var 2) (var 1) one (var 0)) (argumentData (var 3) (var 1) (var 0))) :=
  closeUniv 4 (.impI (.impI (reflection_argument_cross _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineProductReflectionArgument
