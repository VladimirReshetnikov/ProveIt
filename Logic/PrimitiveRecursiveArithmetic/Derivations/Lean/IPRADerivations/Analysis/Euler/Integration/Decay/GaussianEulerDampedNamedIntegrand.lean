import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingKernel

/-!
# The original Euler power with a named damping argument

At a positive rational time t, multiply the actual Euler power t^(z/B-1)
by the exponential of the negative named damping argument. Multiplication
by t then agrees with the actual logarithmic kernel. The power-chart
instance identifies this product with the rescaled pointwise kernel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDampedNamedIntegrand

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (powerF powerData power_regular)
open GaussianEulerExponentialSubstitutionNamedKernel (linearF linearData)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev decayF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (negativeF f)
def decayData (f : PR 2) (x : PTm n) : PTm n := exponentialInputData (negativeF f) (negativeData x)
abbrev nameF (f : PR 2) : PR 2 := multiplyF powerF (decayF f)
def data (f : PR 2) (z B a b x : PTm n) : PTm n := multiplyData powerF (decayF f) (powerData z B a b) (decayData f x)
abbrev weightedF (f : PR 2) : PR 2 := multiplyF constantF (nameF f)
def weightedData (f : PR 2) (z B a b x : PTm n) : PTm n :=
  multiplyData constantF (nameF f) (fraction a b) (data f z B a b x)
abbrev exponentF (f : PR 2) : PR 2 := addF (linearF logF) (negativeF f)
def exponentData (_f : PR 2) (z B a b x : PTm n) : PTm n :=
  addData (linearData logF z B (GaussianPositiveRationalLogarithm.data a b)) (negativeData x)
abbrev logarithmicF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (exponentF f)
def logarithmicData (f : PR 2) (z B a b x : PTm n) : PTm n :=
  exponentialInputData (exponentF f) (exponentData f z B a b x)

@[simp] theorem subst_decayData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    Syn.subst σ (decayData f x) = decayData f (Syn.subst σ x) := by simp [decayData,exponentialInputData]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (z B a b x : PTm n) :
    Syn.subst σ (data f z B a b x) =
      data f (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_weightedData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (z B a b x : PTm n) :
    Syn.subst σ (weightedData f z B a b x) =
      weightedData f (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ x) := by simp [weightedData]
@[simp] theorem subst_exponentData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (z B a b x : PTm n) :
    Syn.subst σ (exponentData f z B a b x) =
      exponentData f (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ x) := by simp [exponentData]
@[simp] theorem subst_logarithmicData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (z B a b x : PTm n) :
    Syn.subst σ (logarithmicData f z B a b x) =
      logarithmicData f (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ x) := by
  simp [logarithmicData,exponentialInputData]

theorem decay_regular (f : PR 2) (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (decayF f) (decayData f x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (negative_fast f x hx))

theorem name_regular (f : PR 2) (z B a b x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x)
    (ht : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f z B a b x) :=
  multiply_fast _ _ _ _ (power_regular z B a b ht) (decay_regular f x hx)

theorem original_time_factor (f : PR 2) (z B a b x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x)
    (ht : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b) :
    Γ ⊢[PRAAx] crossEquivalent (weightedF f) (logarithmicF f)
      (weightedData f z B a b x) (logarithmicData f z B a b x) := by
  let F := GaussianEulerPositiveScalingConstant.nameF
  let X := GaussianEulerPositiveScalingConstant.data z B a b
  let P := GaussianEulerPositiveScalingConstant.scaleF
  let Y := GaussianEulerPositiveScalingConstant.scaleData z B a b
  let D := decayF f
  let d := decayData f x
  let t := fraction a b
  let p := powerData z B a b
  let l := GaussianEulerPositiveScalingConstant.exponentData z B a b
  let v := negativeData x
  have hf := GaussianEulerPositiveScalingConstant.name_regular z B a b ht
  have hp := power_regular z B a b ht
  have hd := decay_regular f x hx
  have hc := constant_regular (Γ := Γ) t
  have he := GaussianEulerPositiveScalingConstant.original_scaling_constant z B a b ht
  have assoc := GaussianNameRingLaws.multiply_associative constantF powerF D t p d hc hp hd
  have products := GaussianGammaAdjacentCutoff.multiply_cross P F D D Y X d d
    (multiply_fast constantF powerF t p hc hp) hf hd hd he (cross_refl _ _ hd)
  have hl := GaussianEulerPositiveScalingConstant.exponent_regular z B a b ht
  have hv := negative_fast f x hx
  have hs := add_fast (linearF logF) (negativeF f) l v hl hv
  have sum := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent
    (linearF logF) (negativeF f) (exponentF f)
    (GaussianNameBounds.U (linearF logF) l) (GaussianNameBounds.U (negativeF f) v)
    (GaussianNameBounds.U (exponentF f) (exponentData f z B a b x))
    l v (exponentData f z B a b x)
    (exponential_input _ _ hl) (exponential_input _ _ hv) (exponential_input _ _ hs) (cross_refl _ _ hs)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc) (cross_trans _ _ _ _ _ _ products sum)

theorem original_power_chart_time_factor (z B e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPowerScalingKernel.source B e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent (weightedF GaussianEulerPositivePowerChart.nameF) GaussianEulerPowerScalingKernel.productF
      (weightedData GaussianEulerPositivePowerChart.nameF z B a b (GaussianEulerPositivePowerChart.data e f d h S a b))
      (GaussianEulerPowerScalingKernel.productData z B e f d h a b) := by
  have hc := GaussianEulerPositivePowerChart.name_regular e f d h Q S E T a b hs.andE₂
  have ht : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b := .andI hs.andE₁ hs.andE₂.andE₂.andE₂.andE₁
  have left := original_time_factor GaussianEulerPositivePowerChart.nameF z B a b
    (GaussianEulerPositivePowerChart.data e f d h S a b) hc ht
  exact cross_trans _ _ _ _ _ _ left (cross_symm _ _ _ _
    (GaussianEulerPowerScalingKernel.original_transformed_kernel z B e f d h Q S E T a b hs))

theorem actual_named_Euler_damping_time_factor_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (pointCN f (var 4) ⋏ GaussianEulerIntegrandName.source (var 0) (var 1) (var 2) (var 3) ⟶
        crossEquivalent (weightedF f) (logarithmicF f)
          (weightedData f (var 0) (var 1) (var 2) (var 3) (var 4))
          (logarithmicData f (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (original_time_factor f _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_power_chart_weighted_integrand_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      (GaussianEulerPowerScalingKernel.source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
        (var 8) (var 9) (var 10) (var 11) ⟶
        crossEquivalent (weightedF GaussianEulerPositivePowerChart.nameF) GaussianEulerPowerScalingKernel.productF
          (weightedData GaussianEulerPositivePowerChart.nameF (var 0) (var 1) (var 10) (var 11)
            (GaussianEulerPositivePowerChart.data (var 2) (var 3) (var 4) (var 5) (var 7) (var 10) (var 11)))
          (GaussianEulerPowerScalingKernel.productData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 10) (var 11))) :=
  closeUniv 12 (.impI (original_power_chart_time_factor _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerDampedNamedIntegrand
