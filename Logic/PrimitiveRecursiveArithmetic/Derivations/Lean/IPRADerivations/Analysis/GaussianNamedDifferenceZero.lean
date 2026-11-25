import IPRADerivations.Analysis.GaussianNamedDifference

/-!
# Equality of regular names through their actual normalized difference
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDifferenceZero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNameRingLaws (equivalent_of_envelope zeroF zero_at zero_fast)
open GaussianNamedDifference (nameF data name_regular sample_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianReconstructionRoots (distance_zero_iff)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem same_clock (F G : PR 2) (x y p : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent F G x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 G p y) two (unit p) := by
  have hu := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hu) hu
    (by ipra_le 0) (cross_at F G x y p p h)

theorem difference_zero (F G : PR 2) (x y z : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN F x) (hG : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] crossEquivalent F G x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF F G) zeroF (data x y) z := by
  apply equivalent_of_envelope _ _ _ _ (num 8) (name_regular _ _ _ _ hF hG) (zero_fast z)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have hf : Δ ⊢[PRAAx] pointCN F (s x) := by simpa [s,Δ,Syn.shift,Fm.shift] using hF.shift
  have hg : Δ ⊢[PRAAx] pointCN G (s y) := by simpa [s,Δ,Syn.shift,Fm.shift] using hG.shift
  have he : Δ ⊢[PRAAx] crossEquivalent F G (s x) (s y) := by simpa [s,Δ,Syn.shift,Fm.shift] using h.shift
  have hp := unit_positive (Γ := Δ) p
  have norm := (distance_zero_iff (qsub (ap2 F p (s x)) (ap2 G p (s y))) two (unit p) hp).iffMpr
    (same_clock F G (s x) (s y) p he)
  have out := distance_triangle_same _ _ _ _ _ _ hp (sample_error F G _ _ p hf hg) norm
  have res : Δ ⊢[PRAAx] distanceBounded (ap2 (nameF F G) p (data (s x) (s y))) (ap2 zeroF p (s z))
      (num 8) (unit p) :=
    distance_congr (.eqRefl _) (zero_at (Γ := Δ) p (s z)).eqSymm (by ipra_ring) (.eqRefl _) out
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,s,Δ,p,Syn.shift,
    GaussianNamedDifference.subst_data,PTm.subst_num] using res

theorem cross_of_zero (F G : PR 2) (x y z : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN F x) (hG : Γ ⊢[PRAAx] pointCN G y)
    (h : Γ ⊢[PRAAx] crossEquivalent (nameF F G) zeroF (data x y) z) :
    Γ ⊢[PRAAx] crossEquivalent F G x y := by
  apply equivalent_of_envelope _ _ _ _ (num 8) hF hG
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have hf : Δ ⊢[PRAAx] pointCN F (s x) := by simpa [s,Δ,Syn.shift,Fm.shift] using hF.shift
  have hg : Δ ⊢[PRAAx] pointCN G (s y) := by simpa [s,Δ,Syn.shift,Fm.shift] using hG.shift
  have he : Δ ⊢[PRAAx] crossEquivalent (nameF F G) zeroF (data (s x) (s y)) (s z) :=
    by simpa [s,Δ,Syn.shift,Fm.shift] using h.shift
  have hp := unit_positive (Γ := Δ) p
  have diff := distance_congr (.eqRefl _) (zero_at (Γ := Δ) p (s z)) (.eqRefl _) (.eqRefl _)
    (same_clock _ _ _ _ p he)
  have raw := distance_triangle_same _ _ _ _ _ _ hp
    (distance_symmetric _ _ _ _ hp (sample_error F G _ _ p hf hg)) diff
  have bound := (distance_zero_iff (qsub (ap2 F p (s x)) (ap2 G p (s y))) _ _ hp).iffMp raw
  have res : Δ ⊢[PRAAx] distanceBounded (ap2 F p (s x)) (ap2 G p (s y)) (num 8) (unit p) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) bound
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,s,Δ,p,Syn.shift,PTm.subst_num] using res

theorem actual_named_difference_zero_iff_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (pointCN F (var 0) ⟶ pointCN G (var 1) ⟶
        Fm.iff (crossEquivalent (nameF F G) zeroF (data (var 0) (var 1)) (var 2))
          (crossEquivalent F G (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (.andI
    (.impI (cross_of_zero F G _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))
    (.impI (difference_zero F G _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianNamedDifferenceZero
