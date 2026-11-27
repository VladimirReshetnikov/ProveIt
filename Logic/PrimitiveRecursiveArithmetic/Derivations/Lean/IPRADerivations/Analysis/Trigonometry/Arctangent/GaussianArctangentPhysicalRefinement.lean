import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialQuadrature
import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.Sampling.GaussianArctangentClampedTarget
import IPRADerivations.Analysis.Trigonometry.Arctangent.Comparisons.GaussianArctangentNamedChord

/-!
# Refinement at the actual arctangent grid width

The original common-refinement proof compares a grid of denominator B*N
with any multiple of it. Retaining B in the estimate gives error at most
4/(B*N). This compares a selected single-grid inverse sample with every
observation of the regular forward name at the selected rational input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentPhysicalRefinement

open_ipra
open GaussianArctangentClampedTarget (nativeValue)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentPartialQuadrature (clearing observation physical_refinement nameF data sample_at mesh mesh_positive)
open GaussianArctangentExponentialPrefix (prefixValue)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem single_grid (j M : PTm n) : Γ ⊢[PRAAx] observation j M one ≐ nativeValue j M := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (prefixValue (var 0) (var 1) (clearing (var 1)) : PTm 2)
    (σ := ![j*one,M*one]) (σ' := ![j,M])
    (fun i => by fin_cases i <;> exact (mul_comm _ one).eqTrans (one_mul _))
  change Γ ⊢[PRAAx] prefixValue (j*one) (M*one) (clearing (M*one)) ≐ prefixValue j M (clearing M)
  simpa only [GaussianArctangentExponentialPrefix.subst_prefixValue,GaussianArctangentPartialQuadrature.subst_clearing,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using e

theorem grid_at (p j M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j M)) (nativeValue j M) (num 4) M := by
  let R := mesh p
  have step : Γ ⊢[PRAAx] observation j M (R*one) ≐ observation j M R := by
    have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![j,M,R*one]) (σ' := ![j,M,R])
      (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact (mul_comm R one).eqTrans (one_mul R))
    simpa only [GaussianArctangentPartialQuadrature.subst_observation,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using e
  exact distance_congr (step.eqTrans (sample_at p j M).eqSymm) (single_grid j M) (.eqRefl _)
    ((mul_comm M one).eqTrans (one_mul M)) (physical_refinement j M one R hM hj (le_refl _) (mesh_positive p))

theorem ordinate_at (p j M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] RationalValueBounds.radius (sndT (ap2 nameF p (data j M))) (sndT (nativeValue j M)) (num 4) M :=
  imaginary_coordinate_radius _ _ _ _ hM (grid_at p j M hM hj)

theorem actual_arctangent_single_grid_forward_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ le (var 1) (var 2) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 1) (var 2))) (nativeValue (var 1) (var 2)) (num 4) (var 2)) :=
  closeUniv 3 (.impI (.impI (grid_at _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentPhysicalRefinement
