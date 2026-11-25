import IPRADerivations.Analysis.GaussianRaabeAffineMean
import IPRADerivations.Analysis.GaussianRaabeStirlingCell
import IPRADerivations.Analysis.GaussianCompactLogarithmBounds
import IPRADerivations.Analysis.GaussianCompactScalarMajorant
import IPRADerivations.Analysis.GaussianRationalPanelTailDistance

/-!
# The elementary Stirling quadrature on a far unit interval

The elementary term is evaluated at the original compact left tags.
The affine comparison retains their
signed mean, with a separate physical bound for the resulting mesh bias.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeStirlingMesh

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianPositiveRationalLogarithm (fraction sample)
open GaussianRaabeLogPrimitiveCell (primitive fraction_bound)
open GaussianRaabeStirlingCell (elementary affine coefficient denominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (canonical qadd qmul positive_product qzero)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianRationalRiemannRefinement (leftSum termsDistance)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def evaluator : PR 3 :=
  PTm.toPR (elementary (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 3)

theorem evaluator_at (p A D x : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluator p (pairT A D) x ≐ elementary p A D := by
  have read : Γ ⊢[PRAAx] ap3 evaluator p (pairT A D) x ≐
      elementary p (fstT (pairT A D)) (sndT (pairT A D)) := by
    simpa only [evaluator,ap3,GaussianRaabeStirlingCell.subst_elementary,subst_fstT,subst_sndT,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (elementary (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 3) ![p,pairT A D,x]
  have pair : Γ ⊢[PRAAx] elementary p (fstT (pairT A D)) (sndT (pairT A D)) ≐ elementary p A D := by
    simpa only [GaussianRaabeStirlingCell.subst_elementary,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (elementary (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![p,fstT (pairT A D),sndT (pairT A D)]) (σ' := ![p,A,D]) (fun i => by
          fin_cases i
          · exact .eqRefl p
          · exact fst_pair A D
          · exact snd_pair A D)
  exact read.eqTrans pair

theorem sample_at (i p N A D : PTm n) :
    Γ ⊢[PRAAx] inst2 (sampleBody evaluator) i (sampleData p N A D D zero) ≐
      elementary p (A*N+D*i) (D*N) :=
  (sample_body_at evaluator i p N A D D zero).eqTrans (evaluator_at p (A*N+D*i) (D*N) zero)

def target (p N A D : PTm n) : PTm n :=
  qsub (primitive p (A*N) (D*N)) (qmul (fraction one (two*N)) (sample p (A*N) (D*N)))

private def data (p N A D : PTm n) : PTm n :=
  GaussianRaabeAffineMean.data N (primitive p (A*N) (D*N)) (sample p (A*N) (D*N))

@[simp] private theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p N A D : PTm n) :
    Syn.subst σ (data p N A D) = data (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ D) := by simp [data]

private theorem cell_error (i p N A D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) (hDA : Γ ⊢[PRAAx] le D A)
    (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (sampleBody evaluator) i (sampleData p N A D D zero))
      (inst2 GaussianRaabeAffineMean.body i (data p N A D)) (coefficient p A D) (denominator p A D) := by
  let a := A*N
  let d := D*N
  let k := primitive p a d
  let s := sample p a d
  have hA := le_trans hD hDA
  have hd := positive_product D N hD hN
  have ha := positive_product A N hA hN
  have hda := mul_le_mul_right N hDA
  have hStep : Γ ⊢[PRAAx] le (D*i) d :=
    le_congr (mul_comm i D) (mul_comm N D) (mul_le_mul_right D (le_of_lt hi))
  have v : Γ ⊢[PRAAx] fraction (D*i) d ≐ fraction i N :=
    GaussianStirlingOddCoefficients.fraction_equal _ _ _ _ hd hN (by dsimp only [d]; ipra_ring)
  have moved : Γ ⊢[PRAAx] affine p a d (D*i) ≐ qadd k (qmul s (GaussianRaabeCenteredMesh.centered i N)) :=
    (qadd_congr (.eqRefl k) (qmul_congr (qsub_congr v (.eqRefl _)) (.eqRefl s))).eqTrans
      (qadd_congr (.eqRefl k) (GaussianRationalPowerAlgebra.qmul_commutative _ _))
  have eh := (GaussianRaabeAffineMean.row_at (Γ := Γ) i N k s).eqTrans moved.eqSymm
  have hu := unit_positive (Γ := Γ) p
  have old := positive_product _ _ (positive_product _ _ ha hd) hu
  have new := positive_product _ _ (positive_product _ _ hA hD) hu
  have bounded : Γ ⊢[PRAAx] distanceBounded (elementary p (a+D*i) d) (affine p a d (D*i))
      (coefficient p A D) (denominator p A D) := distance_radius_mono _ _ _ _ _ _ old new
    (le_of_eq_add (d := zero) (by dsimp only [coefficient,denominator,a,d]; ipra_ring))
    (GaussianRaabeStirlingCell.cell_error p a d (D*i) hd hda hStep)
  exact distance_congr (sample_at i p N A D).eqSymm eh.eqSymm (.eqRefl _) (.eqRefl _) bounded

theorem quadrature_error (p N A D : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hD : Γ ⊢[PRAAx] le one D) (hDA : Γ ⊢[PRAAx] le D A) :
    Γ ⊢[PRAAx] distanceBounded
      (quadrature evaluator p N A D D zero) (target p N A D) (coefficient p A D) (denominator p A D) := by
  let x := sampleData p N A D D zero
  let y := data p N A D
  let g := GaussianRaabeAffineMean.body
  have rows : Γ ⊢[PRAAx] termsDistance (sampleBody evaluator) g N x y (coefficient p A D) (denominator p A D) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s N)::Γ.map Fm.shift
    have sn : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have sd : Δ ⊢[PRAAx] le one (s D) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hD.shift.wk
    have sda : Δ ⊢[PRAAx] le (s D) (s A) := by simpa [Δ,s,Fm.shift,Syn.shift] using hDA.shift.wk
    simpa only [x,y,g,s,Δ,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      subst_data,ConciseIPRA.PTm.subst_zero,GaussianRaabeStirlingCell.coefficient,GaussianRaabeStirlingCell.denominator,
      PTm.subst_add,PTm.subst_mul,LeanProofs.IPRA.PTm.subst_num,GaussianCoefficientNameBounds.subst_unit] using
      cell_error (var 0) (s p) (s N) (s A) (s D) sn sd sda Prf.hyp0
  have hW : Γ ⊢[PRAAx] le one (denominator p A D) :=
    positive_product _ _ (positive_product _ _ (le_trans hD hDA) hD) (unit_positive p)
  have bound := GaussianCompactScalarMajorant.common_mesh_distance (sampleBody evaluator) g N x y D D
    (coefficient p A D) (denominator p A D) hN hD hW rows
  have hk : Γ ⊢[PRAAx] canonical (primitive p (A*N) (D*N)) := GaussianRationalMetric.qsub_canonical _ _
  have mean := GaussianRaabeAffineMean.affine_mean N D (primitive p (A*N) (D*N))
    (sample p (A*N) (D*N)) hN hD hk
  exact distance_congr (.eqRefl _) mean (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hD hW) hW
      (le_of_eq_add (d := zero) (by ipra_ring)) bound)

def biasCost (A : PTm n) : PTm n := GaussianCompactLogarithmBounds.radius one A

theorem correction_bound (p N A D : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hD : Γ ⊢[PRAAx] le one D) (hDA : Γ ⊢[PRAAx] le D A) :
    Γ ⊢[PRAAx] distanceBounded (target p N A D) (primitive p (A*N) (D*N)) (biasCost A) (two*N) := by
  let a := A*N
  let d := D*N
  let v := sample p a d
  let s := fraction one (two*N)
  let K := primitive p a d
  have ha := positive_product A N (le_trans hD hDA) hN
  have hd := positive_product D N hD hN
  have low : Γ ⊢[PRAAx] le d (one*a) :=
    le_congr (.eqRefl _) (one_mul a).eqSymm (mul_le_mul_right N hDA)
  have high : Γ ⊢[PRAAx] le a (A*d) :=
    le_congr (one_mul a) (by dsimp only [d,a]; ipra_ring) (mul_le_mul_right a hD)
  have hv : Γ ⊢[PRAAx] bounded v (biasCost A) one :=
    GaussianCompactLogarithmBounds.sample_bound p a d one A (le_refl one)
      (.andI (.andI ha hd) (.andI low high))
  have hW := positive_product two N RationalAlgebra.two_positive hN
  have bound : Γ ⊢[PRAAx] bounded (qmul s v) (biasCost A) (two*N) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (one_mul _) (by ipra_ring)
      (GaussianRationalReciprocal.bounded_product s v one (two*N) _ one hW (le_refl one)
        (fraction_bound one (two*N) hW) hv)
  have near := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hW).iffMpr bound
  have e : Γ ⊢[PRAAx] qsub K qzero ≐ K :=
    GaussianRationalReconstruction.qsub_zero_right K (GaussianRationalMetric.qsub_canonical _ _)
  exact distance_congr (.eqRefl _) e (by ipra_ring) (.eqRefl _)
    (GaussianNamedDifference.difference_distance K K (qmul s v) qzero zero (biasCost A) (two*N) hW
      (GaussianRationalPowerDifference.distance_refl_zero K _ hW) near)

def errorNumerator (p N A D : PTm n) : PTm n :=
  coefficient p A D*(two*N)+biasCost A*denominator p A D
def errorDenominator (p N A D : PTm n) : PTm n := denominator p A D*(two*N)

theorem primitive_error (p N A D : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hD : Γ ⊢[PRAAx] le one D) (hDA : Γ ⊢[PRAAx] le D A) :
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluator p N A D D zero) (primitive p (A*N) (D*N))
      (errorNumerator p N A D) (errorDenominator p N A D) :=
  GaussianRationalPanelTailDistance.triangle _ _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (le_trans hD hDA) hD) (unit_positive p))
    (positive_product two N RationalAlgebra.two_positive hN)
    (quadrature_error p N A D hN hD hDA) (correction_bound p N A D hN hD hDA)

theorem actual_Stirling_unit_quadrature_primitive_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let p := var 0
       let N := var 1
       let A := var 2
       let D := var 3
       (le one N ⋏ (le one D ⋏ le D A)) ⟶
         distanceBounded (quadrature evaluator p N A D D zero) (primitive p (A*N) (D*N))
           (errorNumerator p N A D) (errorDenominator p N A D)) :=
  closeUniv 4 (.impI (primitive_error _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeStirlingMesh
