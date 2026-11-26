import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinFiniteNested
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinFiniteDampedUpper
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactNamedAdditivity

/-!
# Upper tail at each original finite damped compact observation

Refine the actual compact grid to the shared reciprocal step. Its
left-endpoint majorant is independent of the upper endpoint. An
independently later evaluation clock pays for the monomial degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteCompactUpper

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName (mesh precision)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianGammaZetaMellinFiniteNested (data compact_input)
open GaussianGammaZetaMellinFiniteDampedEvaluator (evaluatorF budget)
open GaussianGammaZetaMellinFiniteDampedModulus (lipschitz)
open GaussianGammaZetaMellinFiniteDampedUpper (coefficient)
open GaussianGammaZetaMellinUpperPoint (degree)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

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
  let K := two*T*T
  let s := (r+degree R)+K
  let t := precision s T
  let M := mesh s L T
  let w := GaussianCompactNamedAdditivity.refined evaluatorF s a W E L T x
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
  have far : Γ ⊢[PRAAx] bounded w (two*coefficient R*E) a :=
    GaussianGammaZetaMellinFiniteDampedUpper.original_grid_bound t M N z R B a W E E T hz hE ha hW
      (GaussianCompactRiemannName.mesh_positive s L T) hE
      (le_congr (.eqRefl _) (mul_comm E T) h.andE₂.andE₂) dt KT
  exact GaussianCompactNamedAdditivity.observation_bound_of_refined evaluatorF r s a W E L T x
    (two*coefficient R*E) a (le_trans (le_add_right r (degree R)) (le_add_right _ _)) hW (le_trans hE ha) hin far

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteCompactUpper
