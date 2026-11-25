import IPRADerivations.Analysis.GaussianEulerNamedPowerScalingImproper
import IPRADerivations.Analysis.GaussianEulerPowerScalingArbitraryTails
import IPRADerivations.Analysis.GaussianNamedDampingPowerCompactBound

/-!
# Either arbitrary physical tail for the actual named damping quadrature

The cutoff is independent of the observation of the two positive real
parameters. Pay for the original compact comparison at a later frozen
index, use the rational tail bound, and retain the original named
observation and affine panel encoding.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingArbitraryTails

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerNamedPowerScalingFormula (source)
open GaussianEulerNamedPowerScalingImproper (scaleBound)
open GaussianEulerNamedPowerScalingFormulaFrozen (original_frozen_source)
open GaussianEulerNamedPowerScalingPowerFrozen (powerClock)
open GaussianEulerPowerChartUniformSchedule (cutoffIndex cutoff_later)
open GaussianEulerPowerScalingArbitraryTails (above below original_upper_tail_bound original_lower_tail_bound)
open GaussianNamedDampingPowerCompact (nameF data)
open GaussianNamedDampingPowerCompactPaid (parameterClock rationalNameData)
open GaussianNamedDampingPowerCompactBound (observationBound original_bound_from_paid_rational)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def outside (F G : PR 2) (s z R B A x E T y H J a W D : PTm n) : Fm PTm n :=
  let j := cutoffIndex s (J*A) (H*R) H (scaleBound F G z R B x E y H)
  below j R A H J T D a W ⋎ above j R A H J E D a

def tailSource (F G : PR 2) (s z R B A x E T y H J a W D U : PTm n) : Fm PTm n :=
  source F G z R B A x E T y H J ⋏
    ((le one a ⋏ (le one D ⋏ le (a+W) (D*U))) ⋏ outside F G s z R B A x E T y H J a W D)

theorem original_tail_bound (F G : PR 2) (s p z R B A x E T y H J a W D U : PTm n)
    (hs : Γ ⊢[PRAAx] tailSource F G s z R B A x E T y H J a W D U) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF F G) p (data z R B x y T J a W D U)) (two*unit p+num 12*unit s) (unit s*unit p) := by
  let C := parameterClock p R T J D U
  let P := powerClock F G zero z R B x E y H
  let k := C+P
  let M := scaleBound F G z R B x E y H
  let j := cutoffIndex s (J*A) (H*R) H M
  let e := numerator G k y
  let f := denominator G k y
  let d := numerator F k x
  let h := denominator F k x
  let term := ap2 GaussianEulerPowerScalingCompactName.nameF p (rationalNameData F G k z R B x y T J a W D U)
  let geom := hs.andE₂.andE₁
  have base := hs.andE₁.andE₁.andE₁.andE₁.andE₂.andE₁
  have src : Γ ⊢[PRAAx] GaussianNamedDampingPowerCompact.source F G z R B x y E T H J a W D U :=
    .andI (.andI (.andI base.andE₁ (.andI geom.andE₂.andE₁ base.andE₂)) (.andI geom.andE₁ geom.andE₂.andE₂))
      (.andI hs.andE₁.andE₂ hs.andE₁.andE₁.andE₂.andE₂)
  have frozen := original_frozen_source F G k z R B A x E T y H J hs.andE₁
  have rsrc : Γ ⊢[PRAAx] GaussianEulerPowerScalingGridSchedule.source z R B A e f d h H J T D U a W :=
    .andI frozen.andE₁ (.andI frozen.andE₂ (.andI geom.andE₂.andE₁ (.andI geom.andE₁
      (le_congr (.eqRefl _) (mul_comm D U) geom.andE₂.andE₂))))
  have inv := GaussianNamedPositiveLogarithm.decoded_domain F k x E T hs.andE₁.andE₂
  have hr : Γ ⊢[PRAAx] le h (d*E) := le_congr (.eqRefl _) (mul_comm E d) inv.andE₂.andE₁
  have bound := GaussianEulerNamedPowerScalingCutoff.frozen_power_bound F G k z R B A x E T y H J hs.andE₁ (le_add_left P C)
  have atZero := GaussianNamedMultiplyRate.sample_bound_at _ _ _ zero bound
  have cap := GaussianEulerPowerChartUniformSchedule.scale_bound_from_zero z B e f d h _ atZero
  have clock := cutoff_later s z R B A e f d h H J M cap
  have eu := hs.andE₁.andE₂.andE₂.andE₁
  have raw : Γ ⊢[PRAAx] bounded term (observationBound two (unit s) (num 11) p) (unit s*unit p) := by
    refine .orE hs.andE₂.andE₂ ?_ ?_
    · exact original_lower_tail_bound s j p z R B A e f d h H J T E D U a W rsrc.wk eu.wk hr.wk clock.wk Prf.hyp0
    · exact original_upper_tail_bound s j p z R B A e f d h H J T E D U a W rsrc.wk eu.wk hr.wk clock.wk Prf.hyp0
  exact bound_congr (.eqRefl _) (by unfold observationBound; ipra_ring) (.eqRefl _)
    (original_bound_from_paid_rational F G p k z R B x y E T H J a W D U two (unit s) (num 11) src
      (le_add_right C P) (unit_positive s) raw)

theorem actual_named_power_damped_Euler_arbitrary_physical_tails_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
      (tailSource F G (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
        (var 11) (var 12) (var 13) (var 14) (var 15) ⟶
        bounded (ap2 (nameF F G) (var 1) (data (var 2) (var 3) (var 4) (var 6) (var 9) (var 8) (var 11)
          (var 12) (var 13) (var 14) (var 15))) (two*unit (var 1)+num 12*unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 16 (.impI (original_tail_bound F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingArbitraryTails
