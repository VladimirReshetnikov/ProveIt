import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerNamedPowerScalingCutoff

/-!
# The actual named power-damped Euler integral is the named Gamma product

The named sampler uses fixed physical endpoints chosen from a uniform
bound on the frozen inverse scale powers. The literal frozen compact
comparison and the named Gamma-side comparison then pay their errors
at independent observation times.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingImproper

open_ipra
open GaussianEulerNamedPowerScalingFormula (source powerF powerData)
open GaussianEulerNamedPowerScalingCutoff (frozenIndex rationalInputAt rationalInput)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scaleBound (F G : PR 2) (z R B x E y H : PTm n) : PTm n :=
  two*(U (powerF F G) (powerData F G z R B x E y H)+num 3)+two

abbrev nameF (F G : PR 2) : PR 2 := GaussianEulerNamedPowerScalingCutoff.nameF F G
def data (F G : PR 2) (z R B A x E T y H J : PTm n) : PTm n :=
  GaussianEulerNamedPowerScalingCutoff.data z R B A x E T y H J (scaleBound F G z R B x E y H)

ipra_subst scaleBound [powerData, GaussianEulerNamedPowerScalingFormula.exponentData, GaussianGammaFiniteApproximantName.exponentialInputData]

ipra_subst data

theorem original_rational_panel_rate (F G : PR 2) (s z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) : Γ ⊢[PRAAx]
    rationalInputAt F G s z R B A x E T y H J (scaleBound F G z R B x E y H) := by
  let M := scaleBound F G z R B x E y H
  let k := frozenIndex F G s z R B A x E T y H J M
  let e := numerator G k y
  let f := denominator G k y
  let d := numerator F k x
  let h := denominator F k x
  have c := GaussianNamedPositiveLogarithm.decoded_domain F k x E T hs.andE₂
  have bound := GaussianEulerNamedPowerScalingCutoff.frozen_power_bound F G k z R B A x E T y H J hs
    (GaussianEulerNamedPowerScalingCutoff.freeze_power_clock F G s z R B A x E T y H J M)
  have zeroBound := GaussianNamedMultiplyRate.sample_bound_at _ _ _ zero bound
  have scale := GaussianEulerPowerChartUniformSchedule.scale_bound_from_zero z B e f d h _ zeroBound
  have rational := GaussianEulerNamedPowerScalingFormulaFrozen.original_frozen_source F G k z R B A x E T y H J hs
  exact GaussianEulerPowerScalingUniformObservation.original_uniform_panel_rate s z R B A e f d h H J T E M
    (.andI rational (.andI (.andI hs.andE₂.andE₂.andE₁
      (le_congr (.eqRefl h) (mul_comm E d) c.andE₂.andE₁)) scale))

theorem original_rational_panels (F G : PR 2) (z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) : Γ ⊢[PRAAx]
    rationalInput F G z R B A x E T y H J (scaleBound F G z R B x E y H) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have h : Γ.map Fm.shift ⊢[PRAAx] source F G (sh z) (sh R) (sh B) (sh A) (sh x) (sh E) (sh T)
      (sh y) (sh H) (sh J) := by simpa [Fm.shift,Syn.shift,sh] using hs.shift
  simpa only [rationalInput,sh,Syn.shift,subst_scaleBound] using
    original_rational_panel_rate F G (var 0) (sh z) (sh R) (sh B) (sh A) (sh x) (sh E) (sh T) (sh y) (sh H) (sh J) h

theorem original_cross (F G : PR 2) (z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) : Γ ⊢[PRAAx]
    crossEquivalent (nameF F G) (GaussianEulerNamedPowerScalingFormula.nameF F G) (data F G z R B A x E T y H J)
      (GaussianEulerNamedPowerScalingFormula.data F G z R B A x E y H J) :=
  GaussianEulerNamedPowerScalingCutoff.original_cross F G z R B A x E T y H J _ hs
    (original_rational_panels F G z R B A x E T y H J hs)

theorem original_observations (F G : PR 2) (p q z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF F G) p (data F G z R B A x E T y H J))
      (ap2 (GaussianEulerNamedPowerScalingFormula.nameF F G) q (GaussianEulerNamedPowerScalingFormula.data F G z R B A x E y H J))
      (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_cross F G z R B A x E T y H J hs)

theorem name_regular (F G : PR 2) (z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) : Γ ⊢[PRAAx]
    pointCN (nameF F G) (data F G z R B A x E T y H J) := by
  have h := original_cross F G z R B A x E T y H J hs
  exact cross_trans _ _ _ _ _ _ h (cross_symm _ _ _ _ h)

theorem actual_original_named_power_damped_Euler_is_Gamma_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        crossEquivalent (nameF F G) (GaussianEulerNamedPowerScalingFormula.nameF F G)
          (data F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
          (GaussianEulerNamedPowerScalingFormula.data F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
            (var 7) (var 8) (var 9))) :=
  closeUniv 10 (.impI (original_cross F G _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_named_power_damped_Euler_name_regular_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        pointCN (nameF F G) (data F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))) :=
  closeUniv 10 (.impI (name_regular F G _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingImproper
