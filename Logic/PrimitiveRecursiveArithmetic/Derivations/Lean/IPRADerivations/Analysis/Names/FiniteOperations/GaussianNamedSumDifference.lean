import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifferenceAlgebra
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues

/-!
# Difference identities for original named Gaussian sums

The same-precision envelopes use the rational sum and difference
identities on the actual normalized name observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianNamedSumDifference

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast sum_distance sum_difference)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (add_sample_error equivalent_of_envelope through_identity)
open GaussianNamedDifference (name_regular sample_error difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_radius_mono)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (qsub distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

private theorem difference_of_sums_at (f g h k : PR 2) (p x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (Diff (addF f g) (addF h k)) p (dd (addData x y) (addData u v)))
      (qsub (qadd (ap2 f p x) (ap2 g p y)) (qadd (ap2 h p u) (ap2 k p v))) (num 12) (unit p) := by
  have hu := unit_positive (Γ := Γ) p
  have far := sample_error (addF f g) (addF h k) (addData x y) (addData u v) p
    (add_fast _ _ _ _ hf hg) (add_fast _ _ _ _ hh hk)
  have near := difference_distance _ _ _ _ _ _ _ hu (add_sample_error f g x y p hf hg) (add_sample_error h k u v p hh hk)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu far near)

private theorem sum_of_differences_at (f g h k : PR 2) (p x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (addF (Diff f h) (Diff g k)) p (addData (dd x u) (dd y v)))
      (qadd (qsub (ap2 f p x) (ap2 h p u)) (qsub (ap2 g p y) (ap2 k p v))) (num 15) (unit p) := by
  have hu := unit_positive (Γ := Γ) p
  have far := add_sample_error (Diff f h) (Diff g k) (dd x u) (dd y v) p
    (name_regular _ _ _ _ hf hh) (name_regular _ _ _ _ hg hk)
  have near := sum_distance _ _ _ _ _ _ _ hu (sample_error f h x u p hf hh) (sample_error g k y v p hg hk)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu far near)

theorem interleave (f g h k : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v) :
    Γ ⊢[PRAAx] crossEquivalent (Diff (addF f g) (addF h k)) (addF (Diff f h) (Diff g k))
      (dd (addData x y) (addData u v)) (addData (dd x u) (dd y v)) := by
  apply equivalent_of_envelope _ _ _ _ (num 27)
    (name_regular _ _ _ _ (add_fast _ _ _ _ hf hg) (add_fast _ _ _ _ hh hk))
    (add_fast _ _ _ _ (name_regular _ _ _ _ hf hh) (name_regular _ _ _ _ hg hk))
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  let p : PTm (n+1) := var 0
  have fs : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have gs : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift
  have hs : Δ ⊢[PRAAx] pointCN h (sh u) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hh.shift
  have ks : Δ ⊢[PRAAx] pointCN k (sh v) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hk.shift
  have both := through_identity _ _ _ _ _ _ _ (unit_positive p)
    (difference_of_sums_at f g h k p (sh x) (sh y) (sh u) (sh v) fs gs hs ks)
    (sum_of_differences_at f g h k p (sh x) (sh y) (sh u) (sh v) fs gs hs ks)
    (sum_difference (ap2 f p (sh x)) (ap2 h p (sh u)) (ap2 g p (sh y)) (ap2 k p (sh v)))
  simpa only [Δ,sh,p,Syn.shift,GaussianNamedDifference.subst_data,GaussianNameArithmetic.subst_addData,PTm.subst_num] using
    distance_congr (.eqRefl _) (.eqRefl _) (show Δ ⊢[PRAAx] num 12+num 15 ≐ num 27 by ipra_ring) (.eqRefl _) both

private theorem cancel_added_at (f g : PR 2) (p x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (Diff (addF f g) f) p (dd (addData x y) x))
      (ap2 g p y) (num 9) (unit p) := by
  let a := ap2 f p x
  let b := ap2 g p y
  have hu := unit_positive (Γ := Γ) p
  have far := sample_error (addF f g) f (addData x y) x p (add_fast _ _ _ _ hf hg) hf
  have near := difference_distance _ _ _ _ _ _ _ hu (add_sample_error f g x y p hf hg)
    (GaussianRationalPowerDifference.distance_refl_zero a (unit p) hu)
  have recode : Γ ⊢[PRAAx] GaussianTranslatedNonconstant.recode b ≐ GaussianFastValueCut.recode b :=
    GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianTranslatedNonconstant.recode_canonical b)
      (GaussianFastValueCut.recode_canonical b) (GaussianRationalL1.raw_den_positive b)
      (GaussianTranslatedNonconstant.recode_represents b) (GaussianFastValueCut.recode_represents b)
  have e := (GaussianRationalSyntheticCoefficientValues.qadd_sub_recode (Γ := Γ) a b).eqTrans recode
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 (Diff (addF f g) f) p (dd (addData x y) x))
      (GaussianFastValueCut.recode b) (num 6+(GaussianNameRingLaws.three+zero)) (unit p) :=
    distance_congr (.eqRefl _) e (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu far near)
  have last : Γ ⊢[PRAAx] distanceBounded (GaussianFastValueCut.recode b) b zero (unit p) :=
    distance_radius_mono _ _ zero one zero (unit p) (le_refl one) hu
    (le_of_eq_add (d := zero) (by ipra_ring)) (GaussianFastValueCut.recode_distance b)
  have radius : Γ ⊢[PRAAx] num 6+(GaussianNameRingLaws.three+zero)+zero ≐ num 9 := by
    unfold GaussianNameRingLaws.three
    ipra_ring
  exact distance_congr (.eqRefl _) (.eqRefl _) radius (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu first last)

theorem cancel_added (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (Diff (addF f g) f) g (dd (addData x y) x) y := by
  apply equivalent_of_envelope _ _ _ _ (num 9) (name_regular _ _ _ _ (add_fast _ _ _ _ hf hg) hf) hg
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have fs : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have gs : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift
  simpa only [Δ,sh,Syn.shift,GaussianNamedDifference.subst_data,GaussianNameArithmetic.subst_addData,PTm.subst_num] using
    cancel_added_at f g (var 0) (sh x) (sh y) fs gs

theorem constant_difference (a b c : PTm n) (hc : Γ ⊢[PRAAx] qsub a b ≐ c) :
    Γ ⊢[PRAAx] crossEquivalent (Diff constantF constantF) constantF (dd a b) c := by
  apply equivalent_of_envelope _ _ _ _ (num 6)
    (name_regular _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  let p : PTm (n+1) := var 0
  have eq : Δ ⊢[PRAAx] qsub (sh a) (sh b) ≐ sh c := by simpa [Δ,sh,Fm.shift,Syn.shift] using hc.shift
  have read := (GaussianRationalSyntheticDivision.qsub_congr (constant_at p (sh a)) (constant_at p (sh b))).eqTrans
    (eq.eqTrans (constant_at p (sh c)).eqSymm)
  simpa only [Δ,sh,p,Syn.shift,GaussianNamedDifference.subst_data,PTm.subst_num] using
    distance_congr (.eqRefl _) read (.eqRefl _) (.eqRefl _)
      (sample_error constantF constantF (sh a) (sh b) p (constant_regular _) (constant_regular _))

theorem actual_named_difference_of_sums_closed (f g h k : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((pointCN f (var 0) ⋏ (pointCN g (var 1) ⋏ (pointCN h (var 2) ⋏ pointCN k (var 3)))) ⟶
        crossEquivalent (Diff (addF f g) (addF h k)) (addF (Diff f h) (Diff g k))
          (dd (addData (var 0) (var 1)) (addData (var 2) (var 3)))
          (addData (dd (var 0) (var 2)) (dd (var 1) (var 3)))) :=
  closeUniv 4 (.impI (interleave f g h k _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedSumDifference
