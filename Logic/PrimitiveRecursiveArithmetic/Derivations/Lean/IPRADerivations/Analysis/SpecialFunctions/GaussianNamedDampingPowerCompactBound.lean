import IPRADerivations.Analysis.SpecialFunctions.GaussianNamedDampingPowerCompactPaid
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianReconstructionRoots

/-!
# Transfer of uniform rational compact bounds to named parameters

A bound on a frozen rational panel at any paid clock transfers to the
actual named damped quadrature with one additional observation unit.
The panel, target radius, and source bounds can be fixed before the
parameter clock is chosen.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompactBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedDampingPowerCompact (source nameF data)
open GaussianNamedDampingPowerCompactPaid (parameterClock rationalNameData original_paid_observations)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianReconstructionRoots (norm_from_distance)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def observationBound (A D H p : PTm n) : PTm n := A*unit p+H*D

private theorem nine_clock (p : PTm n) : Γ ⊢[PRAAx] le (num 9*unit p) (unit (p+num 6)) := by
  have six : Γ ⊢[PRAAx] le (num 6) (unit (num 5)) := RationalClosure.succ_le_two_pow (num 5)
  have factor : Γ ⊢[PRAAx] num 6*two ≐ num 12 := by ipra_ring
  have twelve : Γ ⊢[PRAAx] le (num 12) (unit (num 6)) :=
    le_congr factor (pw_succ two (num 5)).eqSymm (mul_le_mul_right two six)
  have nine : Γ ⊢[PRAAx] le (num 9) (unit (num 6)) :=
    le_trans (le_of_eq_add (d := num 3) (by ipra_ring)) twelve
  exact le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two p (num 6)).eqSymm) (mul_le_mul_right (unit p) nine)

theorem original_bound_from_paid_rational (F G : PR 2) (p k z Rz B x y C₀ C R₀ R a W E T A D H : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T)
    (hk : Γ ⊢[PRAAx] le (parameterClock p Rz C R E T) k) (hd : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] bounded
      (ap2 GaussianEulerPowerScalingCompactName.nameF p (rationalNameData F G k z Rz B x y C R a W E T))
      (observationBound A D H p) (D*unit p)) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF F G) p (data z Rz B x y C R a W E T)) (observationBound A D (H+one) p) (D*unit p) := by
  let K := unit (p+num 6)
  let P := unit p
  let U := observationBound A D H p
  let V := observationBound A D (H+one) p
  let F₀ := ap2 (nameF F G) p (data z Rz B x y C R a W E T)
  have hK := unit_positive (Γ := Γ) (p+num 6)
  have dp := positive_product _ _ hd (unit_positive p)
  have h := norm_from_distance F₀ _ (num 9) K U (D*P) hK dp
    (original_paid_observations F G p k z Rz B x y C₀ C R₀ R a W E T hs hk) hr
  refine bounded_radius_mono F₀ _ _ V (D*P) (positive_product _ _ hK dp) dp ?_ h
  dsimp only [U,V,observationBound]
  ipra_le 𝔞(D*D*P)*sl (nine_clock (Γ := Γ) p)

theorem actual_named_power_damped_compact_bound_from_rational_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18
      (source F G (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
          (var 11) (var 12) (var 13) (var 14) ⟶
        le (parameterClock (var 0) (var 3) (var 8) (var 10) (var 13) (var 14)) (var 1) ⟶ le one (var 16) ⟶
        bounded (ap2 GaussianEulerPowerScalingCompactName.nameF (var 0)
          (rationalNameData F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8) (var 10) (var 11) (var 12) (var 13) (var 14)))
          (observationBound (var 15) (var 16) (var 17) (var 0)) (var 16*unit (var 0)) ⟶
        bounded (ap2 (nameF F G) (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 8) (var 10) (var 11) (var 12) (var 13) (var 14)))
          (observationBound (var 15) (var 16) (var 17+one) (var 0)) (var 16*unit (var 0))) :=
  closeUniv 18 (.impI (.impI (.impI (.impI (original_bound_from_paid_rational F G
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompactBound
