import IPRADerivations.Analysis.Integration.GaussianRationalRiemannRefinement
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# The difference of two actual quadratures on a shared grid

Sum the literal differences at the paired row data and use the same
original grid weight. The proof uses the existing finite sum operations
without requiring canonical input row codes or equal data.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureDifference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianRationalFiniteSum (sum)
open GaussianRationalMatrixFiniteSums (negativeBody sum_negative)
open GaussianRationalRiemannRefinement (leftSum weight)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leftBody (f : PTm 2) : PTm 2 := inst2 f (var 0) (fstT (var 1))
def rightBody (g : PTm 2) : PTm 2 := inst2 g (var 0) (sndT (var 1))
def differenceBody (f g : PTm 2) : PTm 2 := qsub (leftBody f) (rightBody g)

private theorem left_at (f : PTm 2) (i d : PTm n) :
    inst2 (leftBody f) i d = inst2 f i (fstT d) := by
  simp [leftBody,inst2,Syn.subst_subst]
  congr 1
  funext j
  fin_cases j <;> simp

private theorem right_at (g : PTm 2) (i d : PTm n) :
    inst2 (rightBody g) i d = inst2 g i (sndT d) := by
  simp [rightBody,inst2,Syn.subst_subst]
  congr 1
  funext j
  fin_cases j <;> simp

theorem difference_body_at (f g : PTm 2) (i x y : PTm n) :
    Γ ⊢[PRAAx] inst2 (differenceBody f g) i (pairT x y) ≐ qsub (inst2 f i x) (inst2 g i y) := by
  simp only [differenceBody,inst2,GaussianRationalMetric.subst_qsub]
  change Γ ⊢[PRAAx] qsub (inst2 (leftBody f) i (pairT x y)) (inst2 (rightBody g) i (pairT x y)) ≐ _
  rw [left_at,right_at]
  exact qsub_congr (congrInst2 f (.eqRefl i) (fst_pair x y)) (congrInst2 g (.eqRefl i) (snd_pair x y))

private theorem left_sum (f : PTm 2) (N x y : PTm n) :
    Γ ⊢[PRAAx] sum (leftBody f) N (pairT x y) ≐ sum f N x := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simp only [Syn.shift,subst_pairT,left_at]
  exact congrInst2 f (.eqRefl _) (fst_pair _ _)

private theorem right_sum (g : PTm 2) (N x y : PTm n) :
    Γ ⊢[PRAAx] sum (rightBody g) N (pairT x y) ≐ sum g N y := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simp only [Syn.shift,subst_pairT,right_at]
  exact congrInst2 g (.eqRefl _) (snd_pair _ _)

theorem finite_sum_difference (f g : PTm 2) (N x y : PTm n) :
    Γ ⊢[PRAAx] sum (differenceBody f g) N (pairT x y) ≐ qsub (sum f N x) (sum g N y) :=
  (GaussianRationalFiniteSum.sum_add (leftBody f) (negativeBody (rightBody g)) N (pairT x y)).eqTrans
    ((qadd_congr (.eqRefl _) (sum_negative (rightBody g) N (pairT x y))).eqTrans
      (qsub_congr (left_sum f N x y) (right_sum g N x y)))

theorem weighted_difference (f g : PTm 2) (N x y C E : PTm n) :
    Γ ⊢[PRAAx] qsub (leftSum f N x C E) (leftSum g N y C E) ≐
      leftSum (differenceBody f g) N (pairT x y) C E :=
  (GaussianRationalRoundedPower.multiplication_difference (weight C E N) (sum f N x) (sum g N y)).eqTrans
    (qmul_congr (.eqRefl _) (finite_sum_difference f g N x y).eqSymm)

theorem actual_shared_quadrature_difference_closed (f g : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (qsub (leftSum f (var 0) (var 1) (var 3) (var 4)) (leftSum g (var 0) (var 2) (var 3) (var 4)) ≐
        leftSum (differenceBody f g) (var 0) (pairT (var 1) (var 2)) (var 3) (var 4)) :=
  closeUniv 5 (weighted_difference f g _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureDifference
