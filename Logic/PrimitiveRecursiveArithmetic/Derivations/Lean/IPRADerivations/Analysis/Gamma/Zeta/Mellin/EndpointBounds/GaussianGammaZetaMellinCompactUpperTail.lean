import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinCompact
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.EndpointBounds.GaussianGammaZetaMellinUpperGrid
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactNamedAdditivity

/-!
# Uniform upper bound at each original compact Mellin observation

Refine the actual compact grid to the shared reciprocal step. Its
left-endpoint majorant is independent of the upper endpoint. An
independently later evaluation clock pays for the monomial degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinCompactUpperTail

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName (mesh precision)
open GaussianGammaZetaMellinCompact (nameF data source gain compact_input)
open GaussianGammaZetaMellinGrid (evaluatorF fixedData)
open GaussianGammaZetaMellinUpperPoint (coefficientBound degree)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem observation_bound (r z R B a W E H T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a W E H T)
    (ha : Γ ⊢[PRAAx] le E a) (hW : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] bounded (ap2 nameF r (data z R B a W E H T))
      ((two*coefficientBound R*E)*unit r+num 3*a) (a*unit r) := by
  let x := fixedData z B
  let L := gain R H T
  let s := r+degree R
  let t := precision s T
  let M := mesh s L T
  let w := GaussianCompactNamedAdditivity.refined evaluatorF s a W E L T x
  have hE := h.andE₂.andE₁.andE₂
  have hin := compact_input z R B a W E H T h
  have hz : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B :=
    .andI h.andE₁.andE₁ h.andE₁.andE₂.andE₂
  have dt : Γ ⊢[PRAAx] le (degree R) t :=
    le_trans (le_add_left (degree R) r) (le_trans (le_add_right s T) (le_add_right _ _))
  have far : Γ ⊢[PRAAx] bounded w (two*coefficientBound R*E) a :=
    GaussianGammaZetaMellinUpperGrid.upper_grid_bound t M z R B a W E hz hE ha hW
      (GaussianCompactRiemannName.mesh_positive s L T) dt
  exact GaussianCompactNamedAdditivity.observation_bound_of_refined evaluatorF r s a W E L T x
    (two*coefficientBound R*E) a (le_add_right r (degree R)) hW (le_trans hE ha) hin far

theorem actual_original_Mellin_compact_upper_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let r := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let a := var 4
     let W := var 5
     let E := var 6
     let H := var 7
     let T := var 8
     (source z R B a W E H T ⋏ (le E a ⋏ le one W)) ⟶
       bounded (ap2 nameF r (data z R B a W E H T)) ((two*coefficientBound R*E)*unit r+num 3*a) (a*unit r)) :=
  closeUniv 9 (.impI (observation_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinCompactUpperTail
