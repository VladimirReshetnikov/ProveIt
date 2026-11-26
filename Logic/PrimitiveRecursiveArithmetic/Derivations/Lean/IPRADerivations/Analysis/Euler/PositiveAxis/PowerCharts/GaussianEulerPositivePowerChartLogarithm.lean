import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChart
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFoldedApproximantBalance

/-!
# The logarithmic coordinate of the original positive rational power chart

At a rational time t, exponential of log(d/h) + (e/f) log(t)
agrees with the original constant-clock chart at independent precisions.
The power input, the scale input and the chart observations all use the
original programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartLogarithm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChart (argument source scale_bound)
open GaussianEulerIntegrandName (powerExponentF powerExponentData powerRadius powerF powerData)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev logarithmF : PR 2 := addF logF powerExponentF
def logarithmData (e f d h a b : PTm n) : PTm n :=
  addData (GaussianPositiveRationalLogarithm.data d h) (powerExponentData (argument e f) f a b)
abbrev exponentialF : PR 2 := GaussianRadiusExponentialName.nameF logarithmF
def exponentialData (e f d h a b : PTm n) : PTm n :=
  GaussianGammaFiniteApproximantName.exponentialInputData logarithmF (logarithmData e f d h a b)

@[simp] theorem subst_logarithmData {m : ℕ} (σ : Fin n → PTm m) (e f d h a b : PTm n) :
    Syn.subst σ (logarithmData e f d h a b) =
      logarithmData (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h)
        (Syn.subst σ a) (Syn.subst σ b) := by simp [logarithmData]

@[simp] theorem subst_exponentialData {m : ℕ} (σ : Fin n → PTm m) (e f d h a b : PTm n) :
    Syn.subst σ (exponentialData e f d h a b) =
      exponentialData (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h)
        (Syn.subst σ a) (Syn.subst σ b) := by simp [exponentialData,GaussianGammaFiniteApproximantName.exponentialInputData]

theorem power_source (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] GaussianEulerIntegrandName.source (argument e f) f a b :=
  .andI hs.andE₁.andE₁.andE₂ hs.andE₂.andE₂.andE₁

theorem logarithm_regular (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] pointCN logarithmF (logarithmData e f d h a b) :=
  add_fast logF powerExponentF _ _
    (GaussianPositiveRationalLogarithm.name_regular d h hs.andE₁.andE₂.andE₁)
    (GaussianEulerIntegrandName.power_exponent_regular _ _ _ _ (power_source e f d h Q S E T a b hs))

theorem exponential_regular (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] pointCN exponentialF (exponentialData e f d h a b) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (logarithm_regular e f d h Q S E T a b hs))

theorem original_chart (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent exponentialF GaussianEulerPositivePowerChart.nameF
      (exponentialData e f d h a b) (GaussianEulerPositivePowerChart.data e f d h S a b) := by
  let x := GaussianPositiveRationalLogarithm.data d h
  let y := powerExponentData (argument e f) f a b
  let X := GaussianPositiveRationalLogarithm.expData d h
  let Y := powerData (argument e f) f a b
  let c := fraction d h
  let F := GaussianPositiveRationalLogarithm.expF
  have hc := hs.andE₁.andE₂.andE₁
  have hp := power_source e f d h Q S E T a b hs
  have hY : Γ ⊢[PRAAx] pointCN powerF Y := GaussianEulerIntegrandName.power_regular _ _ _ _ hp
  have expSum := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent logF powerExponentF logarithmF
    (GaussianPositiveRationalLogarithm.radius d h) (powerRadius (argument e f) f a b)
    (GaussianNameBounds.U logarithmF (logarithmData e f d h a b)) x y (logarithmData e f d h a b)
    (GaussianPositiveRationalLogarithm.exponential_input d h hc)
    (GaussianEulerIntegrandName.power_input _ _ _ _ hp)
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (logarithm_regular e f d h Q S E T a b hs))
    (cross_refl _ _ (logarithm_regular e f d h Q S E T a b hs))
  have expProduct := GaussianGammaAdjacentCutoff.multiply_cross F constantF powerF powerF X c Y Y
    (GaussianPositiveRationalLogarithm.exponential_regular d h hc) (constant_regular c) hY hY
    (GaussianPositiveRationalLogarithm.exponential_fraction d h hc) (cross_refl _ _ hY)
  have clock := GaussianBoundedConstantProductName.ordinary_product_identity powerF S c Y
    (.andI hY (scale_bound e f d h Q S hs.andE₁))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ expSum)
    (cross_trans _ _ _ _ _ _ expProduct (cross_symm _ _ _ _ clock))

theorem actual_original_power_chart_as_exponential_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        crossEquivalent exponentialF GaussianEulerPositivePowerChart.nameF
          (exponentialData (var 0) (var 1) (var 2) (var 3) (var 8) (var 9))
          (GaussianEulerPositivePowerChart.data (var 0) (var 1) (var 2) (var 3) (var 5) (var 8) (var 9))) :=
  closeUniv 10 (.impI (original_chart _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartLogarithm
