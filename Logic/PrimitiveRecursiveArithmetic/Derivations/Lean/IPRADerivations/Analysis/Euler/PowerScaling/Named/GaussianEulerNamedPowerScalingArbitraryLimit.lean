import IPRADerivations.Analysis.Euler.PowerScaling.Named.GaussianEulerNamedPowerScalingArbitraryPanel

/-!
# Arbitrary enclosing panels converge to the actual improper sampler

The independent compact-to-formula error is preserved under the checked
cross-equivalence between the original improper sampler and its Gamma
formula. There is no additional observation charge for this change of
representative.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingArbitraryLimit

open_ipra
open GaussianEulerNamedPowerScalingArbitraryPanel (panelSource contains)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at)
open GaussianNamedDampingPowerCompact (nameF data name_regular)
open GaussianNameEquivalence (cross_refl)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem subst_contains {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (s z R B A x E T y H J a W D : PTm n) :
    (contains F G s z R B A x E T y H J a W D).subst σ = contains F G (Syn.subst σ s) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ y) (Syn.subst σ H)
      (Syn.subst σ J) (Syn.subst σ a) (Syn.subst σ W) (Syn.subst σ D) := by
  simp [contains, GaussianEulerPowerChartCofinalSchedule.cutoffSize, GaussianEulerPowerChartCofinalEndpoints.lowerDenominator,
    GaussianEulerPowerChartCofinalEndpoints.upperNumerator, GaussianGammaIntegralCutoffs.etaDen, GaussianGammaIntegralCutoffs.top,
    GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]

ipra_subst panelSource [subst_contains]

private theorem subst_formulaData {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (z R B A x E y H J : PTm n) :
    Syn.subst σ (GaussianEulerNamedPowerScalingFormula.data F G z R B A x E y H J) =
      GaussianEulerNamedPowerScalingFormula.data F G (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ x)
        (Syn.subst σ E) (Syn.subst σ y) (Syn.subst σ H) (Syn.subst σ J) := by
  simp [GaussianEulerNamedPowerScalingFormula.data,GaussianEulerNamedPowerScalingFormula.powerData,
    GaussianEulerNamedPowerScalingFormula.exponentData,GaussianEulerNamedPowerScalingFormula.gammaData,
    GaussianGammaFiniteApproximantName.exponentialInputData]

theorem original_formula_rate (F G : PR 2) (s z R B A x E T y H J a W D U : PTm n)
    (hs : Γ ⊢[PRAAx] panelSource F G s z R B A x E T y H J a W D U) : Γ ⊢[PRAAx]
    independentRate (nameF F G) (GaussianEulerNamedPowerScalingFormula.nameF F G) (data z R B x y T J a W D U)
      (GaussianEulerNamedPowerScalingFormula.data F G z R B A x E y H J) two (unit s) := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have p : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] panelSource F G (sh s) (sh z) (sh R) (sh B) (sh A) (sh x)
      (sh E) (sh T) (sh y) (sh H) (sh J) (sh a) (sh W) (sh D) (sh U) :=
    by simpa only [Fm.shift,Syn.shift,subst_panelSource,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate,subst_formulaData,Syn.shift,sh,two,one] using
    GaussianEulerNamedPowerScalingArbitraryPanel.original_observations F G (sh s) (var 1) (var 0) (sh z) (sh R) (sh B)
      (sh A) (sh x) (sh E) (sh T) (sh y) (sh H) (sh J) (sh a) (sh W) (sh D) (sh U) p

theorem original_improper_rate (F G : PR 2) (s z R B A x E T y H J a W D U : PTm n)
    (hs : Γ ⊢[PRAAx] panelSource F G s z R B A x E T y H J a W D U) : Γ ⊢[PRAAx]
    independentRate (nameF F G) (GaussianEulerNamedPowerScalingImproper.nameF F G) (data z R B x y T J a W D U)
      (GaussianEulerNamedPowerScalingImproper.data F G z R B A x E T y H J) two (unit s) := by
  let C := nameF F G
  let X := data z R B x y T J a W D U
  let L := GaussianEulerNamedPowerScalingFormula.nameF F G
  let Y := GaussianEulerNamedPowerScalingFormula.data F G z R B A x E y H J
  let I := GaussianEulerNamedPowerScalingImproper.nameF F G
  let Z := GaussianEulerNamedPowerScalingImproper.data F G z R B A x E T y H J
  have base := hs.andE₁.andE₁.andE₁.andE₁.andE₂.andE₁
  have geom := hs.andE₂.andE₁
  have compact : Γ ⊢[PRAAx] GaussianNamedDampingPowerCompact.source F G z R B x y E T H J a W D U :=
    .andI (.andI (.andI base.andE₁ (.andI geom.andE₂.andE₁ base.andE₂)) (.andI geom.andE₁ geom.andE₂.andE₂))
      (.andI hs.andE₁.andE₂ hs.andE₁.andE₁.andE₂.andE₂)
  exact GaussianNamedRateTransport.transport C L C I X Y X Z two (unit s) (unit_positive s)
    (original_formula_rate F G s z R B A x E T y H J a W D U hs)
    (cross_refl C X (name_regular F G z R B x y E T H J a W D U compact))
    (GaussianEulerNamedPowerScalingImproper.original_cross F G z R B A x E T y H J hs.andE₁)

theorem actual_original_named_power_damped_arbitrary_panels_improper_rate_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
      (panelSource F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
        (var 10) (var 11) (var 12) (var 13) (var 14) ⟶
        independentRate (nameF F G) (GaussianEulerNamedPowerScalingImproper.nameF F G)
          (data (var 1) (var 2) (var 3) (var 5) (var 8) (var 7) (var 10) (var 11) (var 12) (var 13) (var 14))
          (GaussianEulerNamedPowerScalingImproper.data F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
            (var 8) (var 9) (var 10)) two (unit (var 0))) :=
  closeUniv 15 (.impI (original_improper_rate F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingArbitraryLimit
