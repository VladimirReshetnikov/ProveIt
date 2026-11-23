import IPRADerivations.Analysis.GaussianCompactAlignedFourSplit
import IPRADerivations.Analysis.GaussianBetaSharpPartition
import IPRADerivations.Analysis.GaussianBetaSharpFourSplit

/-!
# The actual original eta-to-top grid split at one, N/2 and N

Only the actual aligned-time observation law is assumed. The old even
eta denominator gives exact integer numerator boundaries.
The four actual piece counts are their original numerical widths times
one shared mesh factor. The checked generic split allows all zero widths,
including the middle piece at N=2 and the exterior piece at N=top.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpAlignedFourSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaSharpPartition (lowWidth middleWidth supportTailWidth exteriorWidth halfPoint)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianCompactRiemannName (quadrature)
open GaussianCompactAlignedTime (alignedSamples)
open GaussianRationalHorner (qadd)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCompactAlignedSplit (quadrature_congr)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev pieces (F : PR 3) (s k A R N K x : PTm n) : PTm n :=
  GaussianBetaSharpFourSplit.pieces F s k A R N K x

def source (F : PR 3) (k A R N K x : PTm n) : Fm PTm n :=
  GaussianBetaSharpPartition.source k A R N ⋏ (le one K ⋏ alignedSamples F one (width k A R) (etaDen k A R) x)

theorem total_width (k A R N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    GaussianCompactAlignedFourSplit.totalWidth (lowWidth k A R) (middleWidth k A R N) (supportTailWidth k A R N) (exteriorWidth k A R N) ≐ width k A R := by
  have all := GaussianBetaSharpPartition.exact_partition k A R N h
  have a := natEq all.andE₁
  have b := natEq all.andE₂.andE₁
  have c := natEq all.andE₂.andE₂.andE₁
  have d := natEq all.andE₂.andE₂.andE₂
  have e := natEq (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint (Γ := Γ) k A R)
  apply deriveNat
  unfold GaussianCompactAlignedFourSplit.totalWidth
  ipra_simps
  linear_combination a+b+c+d-e

theorem first_two_endpoint (k A R N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    one+(lowWidth k A R+middleWidth k A R N) ≐ halfPoint k A R N := by
  have all := GaussianBetaSharpPartition.exact_partition k A R N h
  exact (add_assoc _ _ _).eqSymm.eqTrans
    ((congrAdd all.andE₁ (.eqRefl _)).eqTrans all.andE₂.andE₁)

theorem first_three_endpoint (k A R N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaSharpPartition.source k A R N) : Γ ⊢[PRAAx]
    (one+(lowWidth k A R+middleWidth k A R N))+supportTailWidth k A R N ≐ etaDen k A R*N :=
  (congrAdd (first_two_endpoint k A R N h) (.eqRefl _)).eqTrans
    (GaussianBetaSharpPartition.exact_partition k A R N h).andE₂.andE₂.andE₁

/-- Original rational endpoints, actual piece grids and original evaluator. -/
theorem original_sharp_four_piece_split (F : PR 3) (s k A R N K x : PTm n)
    (h : Γ ⊢[PRAAx] source F k A R N K x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s (width k A R*K) one (width k A R) (etaDen k A R) x)
      (pieces F s k A R N K x) (num 4*width k A R) (etaDen k A R*unit s) := by
  let C1 := lowWidth k A R
  let C2 := middleWidth k A R N
  let C3 := supportTailWidth k A R N
  let C4 := exteriorWidth k A R N
  let W := GaussianCompactAlignedFourSplit.totalWidth C1 C2 C3 C4
  have w := total_width k A R N h.andE₁
  have aligned : Γ ⊢[PRAAx] alignedSamples F one W (etaDen k A R) x := by
    have direct := Prf.eqSubst (Γ := Γ) (Ax := PRAAx)
      (alignedSamples F one (var 0) (var 1) (var 2) : Fm PTm 3)
      ![width k A R,etaDen k A R,x] ![W,etaDen k A R,x]
      (fun i => by fin_cases i; exact w.eqSymm; exact .eqRefl _; exact .eqRefl _)
      (by simpa only [GaussianCompactAlignedTime.subst_alignedSamples,Syn.subst_var,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
        ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using h.andE₂.andE₂)
    simpa only [GaussianCompactAlignedTime.subst_alignedSamples,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using direct
  have input : Γ ⊢[PRAAx] GaussianCompactAlignedFourSplit.input F one C1 C2 C3 C4 (etaDen k A R) K x :=
    .andI (le_refl one) (.andI (eta_den_positive k A R) (.andI h.andE₂.andE₁ aligned))
  have old := GaussianCompactAlignedFourSplit.original_four_piece_split F s one C1 C2 C3 C4 (etaDen k A R) K x input
  have all := GaussianBetaSharpPartition.exact_partition k A R N h.andE₁
  have full := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul w (.eqRefl K)) (.eqRefl one) w (.eqRefl (etaDen k A R)) (.eqRefl x)
  have q2 := quadrature_congr (Γ := Γ) F (.eqRefl s) (.eqRefl (C2*K)) all.andE₁ (.eqRefl C2) (.eqRefl (etaDen k A R)) (.eqRefl x)
  have q3 := quadrature_congr (Γ := Γ) F (.eqRefl s) (.eqRefl (C3*K)) (first_two_endpoint k A R N h.andE₁) (.eqRefl C3) (.eqRefl (etaDen k A R)) (.eqRefl x)
  have q4 := quadrature_congr (Γ := Γ) F (.eqRefl s) (.eqRefl (C4*K)) (first_three_endpoint k A R N h.andE₁) (.eqRefl C4) (.eqRefl (etaDen k A R)) (.eqRefl x)
  exact distance_congr full (qadd_congr (qadd_congr (.eqRefl _) q2) (qadd_congr q3 q4)) (congrMul (.eqRefl (num 4)) w) (.eqRefl _) old

/-- Public parameter order matches the original partition first, then
its shared mesh, observation precision and original evaluator data. -/
theorem original_aligned_four_piece_split (F : PR 3) (k A R N K p x : PTm n)
    (h : Γ ⊢[PRAAx] source F k A R N K x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p (width k A R*K) one (width k A R) (etaDen k A R) x)
      (GaussianBetaSharpFourSplit.pieces F p k A R N K x) (num 4*width k A R) (etaDen k A R*unit p) :=
  original_sharp_four_piece_split F p k A R N K x h

theorem original_aligned_sharp_four_actual_grids_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      distanceBounded (quadrature F (var 0) (width (var 1) (var 2) (var 3)*var 5) one
        (width (var 1) (var 2) (var 3)) (etaDen (var 1) (var 2) (var 3)) (var 6))
        (pieces F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (num 4*width (var 1) (var 2) (var 3)) (etaDen (var 1) (var 2) (var 3)*unit (var 0))) :=
  closeUniv 7 (.impI (original_sharp_four_piece_split F _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpAlignedFourSplit
