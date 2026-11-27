import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.Trajectory.GaussianGeneralFTARadiusStep
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.Trajectory.GaussianGeneralFTAResidualStep

/-!
# The actual simultaneous general-FTA trajectory invariant

A single quantifier-free induction proves both the exact position margin
and the changing-polynomial residual bound. The next position is obtained
first from the actual displacement and product recursors. The derived
next disk then justifies the true coefficient-drift bound in the residual
step. Only original coefficient-name coherence and finite apartness are
inputs; no global invariant, disk, residual, Cauchy or output law is given.
All degrees, proof-witness indices, precisions and iteration counters are
internal numbers. The sole external parameter is a fixed PR3 observer.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTAInvariant

open_ipra
open LeanProofs.IPRA.Analysis.GaussianGeneralFTARadiusStep (margin position residual)
open LeanProofs.IPRA.Analysis.GaussianGeneralProductBound (numerator denominator)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTATrajectory (trajectory polynomial delta)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sourceInput)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (B C K R QNum QDen rhoNum)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def joint (a : PR 3) (N h x j : PTm n) : Fm PTm n := position a N h x j ⋏ residual a N h x j
ipra_subst joint

theorem position_zero (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx] position a N h x zero :=
  GaussianRationalReciprocal.bound_congr (GaussianGeneralFTATrajectory.trajectory_zero a N h x).eqSymm
    (GaussianGeneralFTARadiusStep.margin_zero a N h x).eqSymm
    (GaussianGeometricProduct.denominator_zero _ _).eqSymm
    (GaussianMonicResidualRadius.zero_bounded zero one (le_refl one))

theorem residual_zero (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    residual a N h x zero :=
  GaussianRationalReciprocal.bound_congr (.eqRefl _)
    ((congrMul (.eqRefl (B a x)) (pw_zero (QNum N))).eqTrans (by ipra_ring)).eqSymm
    (pw_zero (QDen N)).eqSymm
    (GaussianGeneralFTATrajectory.initial_bound a N h x (Prf.andE₁ hSource))

theorem invariant_zero (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    joint a N h x zero := .andI (position_zero a N h x) (residual_zero a N k h x hSource)

/-- The dependency order proves the next disk before coefficient drift
is applied; the next residual is never used to justify its own disk. -/
theorem invariant_step (a : PR 3) (N k h x j : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) (ih : Γ ⊢[PRAAx] joint a N h x j) : Γ ⊢[PRAAx]
    joint a N h x (succ j) := by
  have nextPosition := GaussianGeneralFTARadiusStep.position_step a N k h x j hSource (Prf.andE₁ ih) (Prf.andE₂ ih)
  have nextDisk := GaussianGeneralFTARadiusStep.point_disk a N h x (succ j)
    (GaussianGeneralFTARadiusStep.source_degree a N k h x hSource) nextPosition
  exact .andI nextPosition
    (GaussianGeneralFTAResidualStep.next_residual_bound a N k h x j hSource (Prf.andE₂ ih) nextDisk)

/-- The induction formula is the conjunction of two QF actual squared
comparisons; unbounded source-name assumptions remain in the context. -/
theorem invariant (a : PR 3) (N k h x j : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    joint a N h x j := by
  have sourceShift : Γ.map Fm.shift ⊢[PRAAx] sourceInput a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralPolynomialSamples.subst_sourceInput,Syn.shift] using hSource.shift
  have all : Γ ⊢[PRAAx] .all (joint a (Syn.shift N) (Syn.shift h) (Syn.shift x) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_joint]
    · exact invariant_zero a N k h x hSource
    · exact invariant_step a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) (var 0) sourceShift.wk Prf.hyp0
  simpa only [subst_joint,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem position_bound (a : PR 3) (N k h x j : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (trajectory a N h x j) (margin a N h x j) (denominator a N h x j) :=
  Prf.andE₁ (invariant a N k h x j hSource)

theorem residual_bound (a : PR 3) (N k h x j : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (evaluate (polynomial a N h x j) (trajectory a N h x j)) (B a x*pw (QNum N) j) (pw (QDen N) j) :=
  Prf.andE₂ (invariant a N k h x j hSource)

theorem point_disk (a : PR 3) (N k h x j : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (trajectory a N h x j) (R a N h x) one :=
  GaussianGeneralFTARadiusStep.point_disk a N h x j (GaussianGeneralFTARadiusStep.source_degree a N k h x hSource)
    (position_bound a N k h x j hSource)

theorem displacement_bound (a : PR 3) (N k h x j : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (delta a N h x j) (numerator a N h x j*C a N h x*pw (rhoNum N) j)
      (denominator a N h x j*pw (K N) j) :=
  GaussianGeneralFTARadiusStep.displacement_bound a N k h x j hSource
    (position_bound a N k h x j hSource) (residual_bound a N k h x j hSource)

theorem displacement_uniform (a : PR 3) (N k h x j : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (delta a N h x j) (R a N h x*C a N h x*pw (rhoNum N) j) (pw (K N) j) := by
  have hN := GaussianGeneralFTARadiusStep.source_degree a N k h x hSource
  have hv := GaussianGeneralProductBound.denominator_positive (Γ := Γ) a N h x j hN
  have hf := RationalNonnegativePowers.denominator_positive (Γ := Γ) (K N) j (GaussianGeneralFTAConstants.K_positive N hN)
  have uniform := mul_le_mul_right (C a N h x*pw (rhoNum N) j*pw (K N) j)
    (GaussianGeneralProductBound.uniform_bound (Γ := Γ) a N h x j hN)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hv hf) hf
    (le_congr (by ipra_ring) (by ipra_ring) uniform) (displacement_bound a N k h x j hSource)

theorem actual_trajectory_invariant_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ joint a (var 0) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (invariant _ _ _ _ _ _ Prf.hyp0))

theorem actual_trajectory_global_bounds_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      (bounded (trajectory a (var 0) (var 2) (var 3) (var 4)) (R a (var 0) (var 2) (var 3)) one ⋏
        bounded (evaluate (polynomial a (var 0) (var 2) (var 3) (var 4)) (trajectory a (var 0) (var 2) (var 3) (var 4)))
          (B a (var 3)*pw (QNum (var 0)) (var 4)) (pw (QDen (var 0)) (var 4)))) :=
  closeUniv 5 (.impI (.andI (point_disk _ _ _ _ _ _ Prf.hyp0) (residual_bound _ _ _ _ _ _ Prf.hyp0)))

theorem actual_trajectory_displacement_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (delta a (var 0) (var 2) (var 3) (var 4))
        (R a (var 0) (var 2) (var 3)*C a (var 0) (var 2) (var 3)*pw (rhoNum (var 0)) (var 4))
        (pw (K (var 0)) (var 4))) :=
  closeUniv 5 (.impI (displacement_uniform _ _ _ _ _ _ Prf.hyp0))

theorem actual_trajectory_program_bounds_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      (bounded (PTm.app (GaussianGeneralFTATrajectory.trajectoryF a) ![var 4,var 0,var 2,var 3])
        (margin a (var 0) (var 2) (var 3) (var 4)) (denominator a (var 0) (var 2) (var 3) (var 4)) ⋏
      bounded (evaluate (polynomial a (var 0) (var 2) (var 3) (var 4))
        (PTm.app (GaussianGeneralFTATrajectory.trajectoryF a) ![var 4,var 0,var 2,var 3]))
          (B a (var 3)*pw (QNum (var 0)) (var 4)) (pw (QDen (var 0)) (var 4)))) :=
  closeUniv 5 (.impI (invariant _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTAInvariant
