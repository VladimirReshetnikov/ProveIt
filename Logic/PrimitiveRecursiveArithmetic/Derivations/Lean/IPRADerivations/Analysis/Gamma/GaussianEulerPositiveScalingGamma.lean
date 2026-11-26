import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositiveScalingImproper
import IPRADerivations.Analysis.Gamma.GaussianEulerIntegralGammaIdentification

/-!
# Original Gamma identification for positive rational linear scaling

The actual cofinal damped quadrature name is identified with the actual
inverse scaling exponential times the original Gamma program. The
positive-scale forward product uses only original named multiplication,
associativity and the verified inverse product. No scaled integral or
Gamma-value identity is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingGamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositiveScalingConstant (inverseF inverseData scaleF scaleData)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Damped" => GaussianEulerPositiveScalingImproper.nameF
local notation "ddata" => GaussianEulerPositiveScalingImproper.data
local notation "Euler" => GaussianEulerImproperName.nameF

def source (z R B A c d : PTm n) : Fm PTm n :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏ (le one c ⋏ le one d)
def productF : PR 2 := multiplyF inverseF gammaF
def productData (z R B A c d : PTm n) : PTm n :=
  multiplyData inverseF gammaF (inverseData z B c d) (gammaData z R B A)
def forwardF : PR 2 := multiplyF scaleF Damped
def forwardData (z R B A c d : PTm n) : PTm n :=
  multiplyData scaleF Damped (scaleData z B c d) (ddata z R B A c d)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A c d : PTm n) :
    (source z R B A c d).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [source]
@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (z R B A c d : PTm n) :
    Syn.subst σ (productData z R B A c d) = productData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [productData]
@[simp] theorem subst_forwardData {m : ℕ} (σ : Fin n → PTm m) (z R B A c d : PTm n) :
    Syn.subst σ (forwardData z R B A c d) = forwardData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [forwardData,GaussianEulerPositiveScalingConstant.scaleData]

theorem improper_source (z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    GaussianEulerPositiveScalingImproper.source z R B A c d :=
  .andI (GaussianEulerIntegralGammaIdentification.improper_source z R B A h.andE₁) h.andE₂

theorem constant_source (z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    GaussianEulerPositiveScalingConstant.source B c d :=
  GaussianEulerPositiveScalingImproper.constant_source z R B A c d (improper_source z R B A c d h)

/-- The actual damped improper name equals exp(-(z/B)*log(c/d))
times the actual original Gamma name. -/
theorem original_scaling_is_Gamma (z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    crossEquivalent Damped productF (ddata z R B A c d) (productData z R B A c d) := by
  have s := improper_source z R B A c d h
  have hi := GaussianEulerPositiveScalingConstant.inverse_regular z B c d (constant_source z R B A c d h)
  have he := GaussianEulerImproperName.name_regular z R B A s.andE₁
  have hg := GaussianEulerIntegralGammaIdentification.original_gamma_regular z R B A h.andE₁
  have replace := GaussianGammaAdjacentCutoff.multiply_cross inverseF inverseF Euler gammaF
    (inverseData z B c d) (inverseData z B c d) (GaussianEulerImproperName.data z R B A) (gammaData z R B A)
    hi hi he hg (cross_refl _ _ hi) (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A h.andE₁)
  exact cross_trans _ _ _ _ _ _ (GaussianEulerPositiveScalingImproper.original_cross z R B A c d s) replace

theorem original_observations (p q z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 Damped p (ddata z R B A c d)) (ap2 productF q (productData z R B A c d))
      (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_scaling_is_Gamma z R B A c d h)

/-- The same original positive scale factor, before cancellation,
recovers the unchanged original Gamma program. -/
theorem original_forward_scaling (z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    crossEquivalent forwardF gammaF (forwardData z R B A c d) (gammaData z R B A) := by
  let x := scaleData z B c d
  let y := inverseData z B c d
  let u := ddata z R B A c d
  let v := gammaData z R B A
  have hs := constant_source z R B A c d h
  have hx := GaussianEulerPositiveScalingCancellation.scale_regular z B c d hs
  have hy := GaussianEulerPositiveScalingConstant.inverse_regular z B c d hs
  have hu := GaussianEulerPositiveScalingImproper.name_regular z R B A c d (improper_source z R B A c d h)
  have hv := GaussianEulerIntegralGammaIdentification.original_gamma_regular z R B A h.andE₁
  have hproduct := multiply_fast inverseF gammaF y v hy hv
  have first := GaussianGammaAdjacentCutoff.multiply_cross scaleF scaleF Damped productF x x u (productData z R B A c d)
    hx hx hu hproduct (cross_refl _ _ hx) (original_scaling_is_Gamma z R B A c d h)
  have regroup := GaussianNameRingLaws.multiply_associative scaleF inverseF gammaF x y v hx hy hv
  have inverse := cross_trans _ _ _ _ _ _ (GaussianNameRingLaws.multiply_commutative scaleF inverseF x y hx hy)
    (cross_trans _ _ _ _ _ _ (GaussianEulerPositiveScalingCancellation.inverse_scale_product z B c d hs)
      (GaussianBoundedInverseApartness.ones_equivalent (GaussianEulerPositiveScalingConstant.exponentData z B c d) v))
  have reduce := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF scaleF inverseF) GaussianNameRingLaws.oneF gammaF gammaF
    (multiplyData scaleF inverseF x y) v v v (multiply_fast scaleF inverseF x y hx hy)
    (GaussianNameRingLaws.one_fast v) hv hv inverse (cross_refl _ _ hv)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ regroup)
    (cross_trans _ _ _ _ _ _ reduce (GaussianNameRingLaws.multiply_one_left gammaF v hv)))

theorem actual_original_positive_linear_scaling_is_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent Damped productF (ddata (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (productData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_scaling_is_Gamma _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_positive_scale_forward_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent forwardF gammaF (forwardData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (gammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 6 (.impI (original_forward_scaling _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingGamma
