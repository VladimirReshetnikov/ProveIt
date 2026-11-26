import IPRADerivations.Analysis.Integration.GaussianRationalRiemannRefinement
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# Uniform norm bounds on actual finite Gaussian sums

A bound for the actual summand at every index below the numerical
length gives the same bound multiplied by the length. The comparison
uses the original zero summands and the original finite sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianUniformFiniteSumBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianReconstructionRoots (distance_zero_iff)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def summandsBounded (f : PTm 2) (N x A B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ bounded (inst2 f (var 0) (Syn.shift x)) (Syn.shift A) (Syn.shift B))

@[simp] theorem subst_summandsBounded {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (N x A B : PTm n) :
    (summandsBounded f N x A B).subst σ =
      summandsBounded f (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) :=
  by simp [summandsBounded,Syn.subst_shift,Syn.shift_subst]

theorem summand_bound_at (f : PTm 2) (N x A B i : PTm n)
    (h : Γ ⊢[PRAAx] summandsBounded f N x A B) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] bounded (inst2 f i x) A B := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ bounded (inst2 f i x) A B := by
    simpa only [summandsBounded,Fm.subst_imp,subst_lt,GaussianRationalMetric.subst_bounded,
      subst_inst2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE rule hi

theorem uniform_sum_bound (f : PTm 2) (N x A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] summandsBounded f N x A B) :
    Γ ⊢[PRAAx] bounded (sum f N x) (N*A) B := by
  let g : PTm 2 := qzero
  have row : Γ ⊢[PRAAx] termsDistance f g N x zero A B := by
    refine .allI (.impI ?_)
    have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
    have hs : Γ.map Fm.shift ⊢[PRAAx] summandsBounded f (Syn.shift N) (Syn.shift x) (Syn.shift A) (Syn.shift B) :=
      by simpa [Fm.shift,Syn.shift] using h.shift
    have input := summand_bound_at f _ _ _ _ (var 0) hs.wk Prf.hyp0
    simpa only [termsDistance,g,inst2,GaussianRationalHorner.subst_qzero,ConciseIPRA.PTm.subst_zero] using
      (distance_zero_iff _ _ _ b.wk).iffMpr input
  have zeroRows : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.zeroTerms g N zero := by
    refine .allI (.impI ?_)
    simp only [g,inst2,GaussianRationalHorner.subst_qzero]
    exact .eqRefl _
  have eq := GaussianRationalMatrixFiniteSums.sum_zero_of_terms g N zero zeroRows
  exact (distance_zero_iff _ _ _ hB).iffMp
    (GaussianRationalDistanceOrder.distance_congr (.eqRefl _) eq (.eqRefl _) (.eqRefl _)
      (sum_distance f g N x zero A B hB row))

theorem actual_uniform_finite_sum_bound_closed (f : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 3) ⟶ summandsBounded f (var 0) (var 1) (var 2) (var 3) ⟶
        bounded (sum f (var 0) (var 1)) (var 0*var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (uniform_sum_bound f _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianUniformFiniteSumBound
