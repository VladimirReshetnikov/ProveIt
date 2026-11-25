import IPRADerivations.Analysis.GaussianNamedDampingPowerChart
import IPRADerivations.Analysis.GaussianGammaCompactCutoffAlignment

/-!
# The named power chart specializes to the original rational chart

When the two fixed names are the exact rational constants d/h and e/f,
the exponent data agree with the actual original Euler power code.
The base coefficient product then matches the original bounded clock
at independent observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerRational

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedDampingPowerChart (exponentData powerF powerData nameF data)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerPositivePowerChart (argument)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem rational_exponent_data (e f a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) : Γ ⊢[PRAAx]
    exponentData constantF (fraction e f) a b ≐ GaussianEulerIntegrandName.powerExponentData (argument e f) f a b := by
  let L := GaussianPositiveRationalLogarithm.logF
  let x := GaussianPositiveRationalLogarithm.data a b
  have eq := (GaussianEulerPositivePowerChart.coefficient_exact e f hf).eqSymm
  change Γ ⊢[PRAAx] multiplyData constantF L (fraction e f) x ≐
    multiplyData constantF L (GaussianEulerIntegrandName.coefficient (argument e f) f) x
  simpa only [GaussianNameArithmetic.subst_multiplyData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (multiplyData constantF L (var 0) (Syn.shift x)) eq

theorem rational_power_data (e f a b : PTm n) (hf : Γ ⊢[PRAAx] le one f) : Γ ⊢[PRAAx]
    powerData constantF (fraction e f) a b ≐ GaussianEulerIntegrandName.powerData (argument e f) f a b := by
  let G := GaussianEulerIntegrandName.powerExponentF
  let x := exponentData constantF (fraction e f) a b
  let y := GaussianEulerIntegrandName.powerExponentData (argument e f) f a b
  have eq : Γ ⊢[PRAAx] x ≐ y := rational_exponent_data e f a b hf
  have radius : Γ ⊢[PRAAx] GaussianNameBounds.U G x ≐ GaussianNameBounds.U G y := by
    simpa only [GaussianNameBounds.subst_U,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (GaussianNameBounds.U G (var 0)) eq
  exact congrPairT radius eq

theorem actual_rational_chart (e f d h Q S E T a b : PTm n)
    (hc : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    crossEquivalent (nameF constantF constantF) GaussianEulerPositivePowerChart.nameF
      (data constantF constantF (fraction d h) (fraction e f) a b)
      (GaussianEulerPositivePowerChart.data e f d h S a b) := by
  let F := GaussianEulerIntegrandName.powerF
  let x := powerData constantF (fraction e f) a b
  let y := GaussianEulerIntegrandName.powerData (argument e f) f a b
  let c := fraction d h
  let z := multiplyData constantF F c y
  let out := GaussianEulerPositivePowerChart.data e f d h S a b
  have ht := GaussianEulerPositivePowerChartLogarithm.power_source e f d h Q S E T a b hc
  have hr := GaussianEulerIntegrandName.power_regular _ _ _ _ ht
  have hf := hc.andE₁.andE₁.andE₂
  have he : Γ ⊢[PRAAx] x ≐ y := rational_power_data e f a b hf
  have combine : Γ ⊢[PRAAx] data constantF constantF c (fraction e f) a b ≐ z := by
    change Γ ⊢[PRAAx] multiplyData constantF F c x ≐ multiplyData constantF F c y
    simpa only [GaussianNameArithmetic.subst_multiplyData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (multiplyData constantF F (Syn.shift c) (var 0)) he
  have original := GaussianBoundedConstantProductName.ordinary_product_identity F S c y
    (.andI hr (GaussianEulerPositivePowerChart.scale_bound e f d h Q S hc.andE₁))
  exact cross_data_congr (multiplyF constantF F) GaussianEulerPositivePowerChart.nameF z _ out out
    combine.eqSymm (.eqRefl _) (cross_symm _ _ _ _ original)

theorem actual_named_power_chart_rational_specialization_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (GaussianEulerPositivePowerChart.source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
        (var 7) (var 8) (var 9) ⟶ crossEquivalent (nameF constantF constantF) GaussianEulerPositivePowerChart.nameF
        (data constantF constantF (fraction (var 2) (var 3)) (fraction (var 0) (var 1)) (var 8) (var 9))
        (GaussianEulerPositivePowerChart.data (var 0) (var 1) (var 2) (var 3) (var 5) (var 8) (var 9))) :=
  closeUniv 10 (.impI (actual_rational_chart _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerRational
