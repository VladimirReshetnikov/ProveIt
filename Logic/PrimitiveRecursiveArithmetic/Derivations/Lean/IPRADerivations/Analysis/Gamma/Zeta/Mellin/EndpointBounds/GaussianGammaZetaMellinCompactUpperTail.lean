import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinCompact
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.EndpointBounds.GaussianGammaZetaMellinUpperGrid
import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity

/-!
# Uniform upper bound at each original compact Mellin observation

Refine the actual compact grid to the shared reciprocal step. Its
left-endpoint majorant is independent of the upper endpoint. An
independently later evaluation clock pays for the monomial degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinCompactUpperTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (mesh precision dyadic_six_lower)
open GaussianGammaZetaMellinCompact (nameF data source gain compact_input regular)
open GaussianGammaZetaMellinGrid (evaluatorF fixedData)
open GaussianGammaZetaMellinUpperPoint (coefficientBound degree)
open GaussianNameEquivalence (point_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalReciprocal (bound_congr)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem observation_bound (r z R B a W E H T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a W E H T)
    (ha : Γ ⊢[PRAAx] le E a) (hW : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] bounded (ap2 nameF r (data z R B a W E H T))
      ((two*coefficientBound R*E)*unit r+num 3*a) (a*unit r) := by
  let x := fixedData z B
  let L := gain R H T
  let d := data z R B a W E H T
  let s := r+degree R
  let t := precision s T
  let M := mesh s L T
  let u := ap2 nameF r d
  let v := ap2 nameF s d
  let w := GaussianCompactNamedAdditivity.refined evaluatorF s a W E L T x
  let U := unit r
  let V := unit s
  let S := unit (s+num 6)
  have hU := unit_positive (Γ := Γ) r
  have hV := unit_positive (Γ := Γ) s
  have hE := h.andE₂.andE₁.andE₂
  have hin := compact_input z R B a W E H T h
  have hz : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B :=
    .andI h.andE₁.andE₁ h.andE₁.andE₂.andE₂
  have dt : Γ ⊢[PRAAx] le (degree R) t :=
    le_trans (le_add_left (degree R) r) (le_trans (le_add_right s T) (le_add_right _ _))
  have grow : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right r (degree R))
  have far : Γ ⊢[PRAAx] bounded w (two*coefficientBound R*E) a :=
    GaussianGammaZetaMellinUpperGrid.upper_grid_bound t M z R B a W E hz hE ha hW
      (GaussianCompactRiemannName.mesh_positive s L T) dt
  have first : Γ ⊢[PRAAx] distanceBounded u v two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hV) hU
      (by change Γ ⊢[PRAAx] le ((U+V)*U) (two*(U*V)); ipra_le 𝔞(U)*sl grow)
      (point_at nameF d r s (regular z R B a W E H T h))
  have mid := GaussianCompactNamedAdditivity.refinement_distance evaluatorF s a W E L T x hW hin
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) evaluatorF s a W E L T x
  have last : Γ ⊢[PRAAx] distanceBounded v w one U :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive _) hU
      (le_congr (.eqRefl _) (one_mul _).eqSymm
        (le_trans (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 3) grow))
          (dyadic_six_lower s)))
      (distance_symmetric _ _ _ _ (unit_positive _)
        (distance_congr (.eqRefl _) read.eqSymm (.eqRefl _) (.eqRefl S) mid))
  have distance : Γ ⊢[PRAAx] distanceBounded u w (num 3) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hU first last)
  exact bound_congr (.eqRefl _) (by ipra_ring) (mul_comm _ _)
    (GaussianReconstructionRoots.norm_from_distance u w (num 3) U _ a hU (le_trans hE ha) distance far)

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
