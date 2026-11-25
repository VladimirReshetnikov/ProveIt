import IPRADerivations.Analysis.GaussianGammaZetaMellinFiniteNested
import IPRADerivations.Analysis.GaussianGammaZetaMellinFiniteDampedUpper
import IPRADerivations.Analysis.GaussianCompactNamedAdditivity

/-!
# Upper tail at each original finite damped compact observation

Refine the actual compact grid to the shared reciprocal step. Its
left-endpoint majorant is independent of the upper endpoint. An
independently later evaluation clock pays for the monomial degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteCompactUpper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (mesh precision dyadic_six_lower)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianGammaZetaMellinFiniteNested (data compact_input)
open GaussianGammaZetaMellinFiniteDampedEvaluator (evaluatorF budget)
open GaussianGammaZetaMellinFiniteDampedModulus (lipschitz)
open GaussianGammaZetaMellinFiniteDampedUpper (coefficient)
open GaussianGammaZetaMellinUpperPoint (degree)
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

local notation "F" => GaussianCompactRiemannName.nameF evaluatorF
local notation "fd" => GaussianGammaZetaMellinFiniteDampedEvaluator.data

theorem observation_bound (r z R B N a W E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a W E T)
    (ha : Γ ⊢[PRAAx] le E a) (hW : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] bounded (ap2 F r (data z R B N (budget R E T N) a W E T))
      ((two*coefficient R*E)*unit r+num 3*a) (a*unit r) := by
  let Q := budget R E T N
  let x := fd z B N Q
  let L := lipschitz N R E T
  let d := data z R B N Q a W E T
  let K := two*T*T
  let s := (r+degree R)+K
  let t := precision s T
  let M := mesh s L T
  let u := ap2 F r d
  let v := ap2 F s d
  let w := GaussianCompactNamedAdditivity.refined evaluatorF s a W E L T x
  let U := unit r
  let V := unit s
  let S := unit (s+num 6)
  have hU := unit_positive (Γ := Γ) r
  have hV := unit_positive (Γ := Γ) s
  have hE := h.andE₁.andE₂.andE₁
  have hQ : Γ ⊢[PRAAx] le N Q :=
    le_of_eq_add (d := N*GaussianGammaZetaMellinDampedPoint.cost R E T) (by dsimp only [Q,budget]; ipra_ring)
  have hin := compact_input z R B N Q a W E T h hQ
  have hz : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B :=
    .andI h.andE₁.andE₁ h.andE₁.andE₂.andE₂
  have later : Γ ⊢[PRAAx] le s t := le_trans (le_add_right s T) (le_add_right _ _)
  have dt : Γ ⊢[PRAAx] le (degree R) t :=
    le_trans (le_add_left (degree R) r) (le_trans (le_add_right (r+degree R) K) later)
  have KT : Γ ⊢[PRAAx] le K (unit t) :=
    le_trans (le_add_left K (r+degree R))
      (le_trans later (le_trans (le_succ_self t) (RationalClosure.succ_le_two_pow t)))
  have grow : Γ ⊢[PRAAx] le U V :=
    GaussianExponentialReference.unit_monotone (le_trans (le_add_right r (degree R)) (le_add_right _ _))
  have far : Γ ⊢[PRAAx] bounded w (two*coefficient R*E) a :=
    GaussianGammaZetaMellinFiniteDampedUpper.original_grid_bound t M N z R B a W E E T hz hE ha hW
      (GaussianCompactRiemannName.mesh_positive s L T) hE
      (le_congr (.eqRefl _) (mul_comm E T) h.andE₂.andE₂) dt KT
  have first : Γ ⊢[PRAAx] distanceBounded u v two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hV) hU
      (by change Γ ⊢[PRAAx] le ((U+V)*U) (two*(U*V)); ipra_le 𝔞(U)*sl grow)
      (point_at F d r s (GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ hin))
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

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteCompactUpper
