import IPRADerivations.Analysis.GaussianArctangentPartialQuadrature
import IPRADerivations.Analysis.GaussianArctangentQuarterExponential
import IPRADerivations.Analysis.GaussianArctangentCayleyBudget

/-!
# Agreement of the partial arctangent name with the original π endpoint

At the unit endpoint the two names take the same rational left sums on
different grids. The finite common refinement gives their equivalence
at independent precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentPartialUnitEndpoint

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentPartialQuadrature (nameF data mesh sample_at observation clearing finite_comparison mesh_positive
  name_regular)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianArctangentExponentialPrefix (prefixValue at_pi_observation)
open GaussianArctangentCayleyBudget (mesh_ge_unit)
open GaussianGammaHalfPiName (meshAt)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem unit_mesh_readback (K : PTm n) : Γ ⊢[PRAAx]
    observation one one K ≐ prefixValue K K (clearing K) := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (prefixValue (var 0) (var 0) (two*(var 0*var 0)) : PTm 1)
    (σ := fun _ => one*K) (σ' := fun _ => K) (fun _ => one_mul K)
  change Γ ⊢[PRAAx] prefixValue (one*K) (one*K) (two*((one*K)*(one*K))) ≐ prefixValue K K (two*(K*K))
  simp only [GaussianArctangentExponentialPrefix.subst_prefixValue,PTm.subst_mul,Syn.subst_var,two,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] at e
  exact e

theorem unit_endpoint_distance (p z : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data one one)) (ap2 quarterF p z) (num 5) (unit p) := by
  let N := mesh p
  let K := meshAt p
  have hN : Γ ⊢[PRAAx] le one N := mesh_positive p
  have hK : Γ ⊢[PRAAx] le one K := le_trans (unit_positive p) (mesh_ge_unit p)
  have h := finite_comparison one one N K (le_refl one) (le_refl one) hN hK
  have budget : Γ ⊢[PRAAx] le ((num 4*K+num 4*N)*unit p) (num 5*(N*K)) := by
    have hk := mesh_ge_unit (Γ := Γ) p
    unfold N mesh
    ipra_le 16*𝔞 (unit p)*sl hk
  have ha : Γ ⊢[PRAAx] observation one one K ≐ ap2 quarterF p z :=
    (unit_mesh_readback K).eqTrans ((at_pi_observation p z).eqTrans
      (GaussianArctangentQuarterExponential.sample_at p z).eqSymm)
  exact distance_congr (sample_at p one one).eqSymm ha (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hN hK) (unit_positive p) budget h)

theorem unit_endpoint_cross (z : PTm n) : Γ ⊢[PRAAx] crossEquivalent nameF quarterF (data one one) z := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (num 5)
    (name_regular one one (le_refl _) (le_refl _)) (quarter_regular z)
  refine .allI ?_
  simpa [GaussianNamedDiagonalRate.diagonalRate,data,Syn.shift] using
    (unit_endpoint_distance (Γ := Γ.map Fm.shift) (var 0) (Syn.shift z))

theorem actual_original_partial_arctangent_agrees_with_pi_endpoint_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (crossEquivalent nameF quarterF (data one one) (var 0)) :=
  closeUniv 1 (unit_endpoint_cross _)

end LeanProofs.IPRA.Analysis.GaussianArctangentPartialUnitEndpoint
