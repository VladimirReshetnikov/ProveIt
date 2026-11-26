import IPRADerivations.Analysis.Integration.GaussianPartitionedFiniteSumDistance
import IPRADerivations.Analysis.Euler.GaussianEulerDampedTimeRate

/-!
# Replace exact integer-cell weights by signed rational widths

The original grouped rows carry the original natural block lengths.
After multiplication by 1/M, each weight is exactly length/M.
Replacing these weights by any signed Gaussian rows costs the width
error times the actual coarse value bound, summed over the block count.
The width rows and their products are the actual finite evaluators.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPartitionedFiniteSumWeightReplacement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPartitionedFiniteSumDistance (blockLength coarseBody coarse_at)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (qmul subst_qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalNaturalScale (natScale)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowSource (cut : PR 2) (g w : PTm 2) (K d y M H A D : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift K) ⟶
    (bounded (inst2 g (var 0) (Syn.shift y)) (Syn.shift H) one ⋏
     distanceBounded (fraction (blockLength cut (var 0) (Syn.shift d)) (Syn.shift M))
       (inst2 w (var 0) (Syn.shift y)) (Syn.shift A) (Syn.shift D)))

@[simp] theorem subst_rowSource {m : ℕ} (σ : Fin n → PTm m) (cut : PR 2) (g w : PTm 2) (K d y M H A D : PTm n) :
    (rowSource cut g w K d y M H A D).subst σ = rowSource cut g w (Syn.subst σ K)
      (Syn.subst σ d) (Syn.subst σ y) (Syn.subst σ M) (Syn.subst σ H) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [rowSource,Syn.subst_shift,Syn.shift_subst]

theorem original_rescale (M t q : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    qmul (fraction one M) (natScale t q) ≐ qmul q (fraction t M) := by
  have width : Γ ⊢[PRAAx] qmul (fraction one M) (GaussianRationalNaturalScale.naturalPoint t) ≐ fraction t M :=
    (GaussianEulerDampedTimeRate.fraction_product one M t one hM (le_refl one)).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (one_mul _) (by ipra_ring))
  exact (qmul_congr (.eqRefl _) (GaussianRationalNaturalScale.natScale_as_product t q)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr width (.eqRefl _)).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _)))

theorem source_at (cut : PR 2) (g w : PTm 2) (K d y M H A D i : PTm n)
    (h : Γ ⊢[PRAAx] rowSource cut g w K d y M H A D) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] bounded (inst2 g i y) H one ⋏
      distanceBounded (fraction (blockLength cut i d) M) (inst2 w i y) A D := by
  have rule := h.allE i
  simp only [Fm.subst_imp,Fm.subst_and,subst_lt,GaussianRationalMetric.subst_bounded,
    GaussianRationalMetric.subst_distanceBounded,subst_inst2,GaussianPositiveRationalLogarithm.subst_fraction,
    GaussianPartitionedFiniteSumDistance.subst_blockLength,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at rule
  exact .impE rule hi

theorem original_row_error (cut : PR 2) (g w : PTm 2) (K d y M H A D i : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rowSource cut g w K d y M H A D) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (multiplyBody (coarseBody cut g)) i (pairT (fraction one M) (pairT d y)))
      (inst2 (qmul g w) i y) (H*A) D := by
  let value := inst2 g i y
  let u := fraction (blockLength cut i d) M
  let v := inst2 w i y
  have hs := source_at cut g w K d y M H A D i h hi
  have left := (multiply_body_at (coarseBody cut g) (fraction one M) i (pairT d y)).eqTrans
    ((qmul_congr (.eqRefl _) (coarse_at cut g i d y)).eqTrans (original_rescale M _ value hM))
  have raw : Γ ⊢[PRAAx] distanceBounded (qmul value u) (qmul value v) (H*A) D :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference value u v).eqSymm
      (.eqRefl _) (one_mul _)
      (GaussianRationalReciprocal.bounded_product value (GaussianRationalMetric.qsub u v) H one A D
        (le_refl one) hD hs.andE₁ hs.andE₂)
  have right : inst2 (qmul g w) i y = qmul value v := by simp [inst2,value,v]
  rw [right]
  exact distance_congr left.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw

theorem original_finite_replacement (cut : PR 2) (g w : PTm 2) (K d y M H A D : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rowSource cut g w K d y M H A D) :
    Γ ⊢[PRAAx] distanceBounded (qmul (fraction one M) (sum (coarseBody cut g) K (pairT d y)))
      (sum (qmul g w) K y) (K*(H*A)) D := by
  let f := multiplyBody (coarseBody cut g)
  let x := pairT (fraction one M) (pairT d y)
  have rows : Γ ⊢[PRAAx] termsDistance f (qmul g w) K x y (H*A) D := by
    let s (u : PTm n) := Syn.shift u
    have hs : Γ.map Fm.shift ⊢[PRAAx] rowSource cut g w (s K) (s d) (s y) (s M) (s H) (s A) (s D) :=
      by simpa [Fm.shift,Syn.shift,s] using h.shift
    have ms : Γ.map Fm.shift ⊢[PRAAx] le one (s M) := by simpa [Fm.shift,Syn.shift,s] using hM.shift
    have ds : Γ.map Fm.shift ⊢[PRAAx] le one (s D) := by simpa [Fm.shift,Syn.shift,s] using hD.shift
    refine .allI (.impI ?_)
    simpa only [termsDistance,f,x,subst_pairT,GaussianPositiveRationalLogarithm.subst_fraction,PTm.subst_mul,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,s] using
      original_row_error cut g w (s K) (s d) (s y) (s M) (s H) (s A) (s D) (var 0) ms.wk ds.wk hs.wk Prf.hyp0
  exact distance_congr (sum_multiply (coarseBody cut g) (fraction one M) K (pairT d y)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (sum_distance f (qmul g w) K x y (H*A) D hD rows)

theorem actual_original_partition_weight_replacement_closed (cut : PR 2) (g w : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((le one (var 3) ⋏ (le one (var 6) ⋏ rowSource cut g w (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) ⟶
        distanceBounded (qmul (fraction one (var 3)) (sum (coarseBody cut g) (var 0) (pairT (var 1) (var 2))))
          (sum (qmul g w) (var 0) (var 2)) (var 0*(var 4*var 5)) (var 6)) :=
  closeUniv 7 (.impI (original_finite_replacement cut g w _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPartitionedFiniteSumWeightReplacement
