import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.NamedIncrements.GaussianNamedIncrementDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift

/-!
# Finite product rule for a common regular named increment

An apartness certificate for the increment suffices for an exact identity
between the original normalized names. The reciprocal uses the supplied
increment at both endpoint differences.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedIncrementProductRule

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianNameArithmetic (addF addData add_fast add_equivalent multiplyF
  multiplyData multiply_fast multiplyModulus multiply_equivalent sum_distance)
open GaussianNameEquivalence (diagonal_refl crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianNameRingLaws (three multiply_sample_error add_sample_error product_right_error
  equivalent_of_envelope distributive multiply_associative multiply_commutative multiply_one_left)
open GaussianRationalDistanceOrder (distance_triangle_same)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianGammaAdjacentCutoff renaming swap_first → swap_adjacent

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "DF" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "QF" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "qd" => GaussianNamedIncrementDifferenceQuotient.data

def lhsF (I1 I0 G1 G0 K : PR 2) : PR 2 :=
  QF (multiplyF I1 G1) (multiplyF I0 G0) K

def lhsData (I1 I0 G1 G0 K : PR 2) (i1 i0 g1 g0 z a : PTm n) : PTm n :=
  qd (multiplyF I1 G1) (multiplyF I0 G0) K
    (multiplyData I1 G1 i1 g1) (multiplyData I0 G0 i0 g0) z a

def rhsF (I1 I0 G1 G0 K : PR 2) : PR 2 :=
  addF (multiplyF I1 (QF G1 G0 K)) (multiplyF G0 (QF I1 I0 K))

def rhsData (I1 I0 G1 G0 K : PR 2) (i1 i0 g1 g0 z a : PTm n) : PTm n :=
  addData (multiplyData I1 (QF G1 G0 K) i1 (qd G1 G0 K g1 g0 z a))
    (multiplyData G0 (QF I1 I0 K) g0 (qd I1 I0 K i1 i0 z a))

ipra_subst lhsData

ipra_subst rhsData

theorem lhs_regular (I1 I0 G1 G0 K : PR 2) (i1 i0 g1 g0 z a : PTm n)
    (hi1 : Γ ⊢[PRAAx] pointCN I1 i1) (hi0 : Γ ⊢[PRAAx] pointCN I0 i0)
    (hg1 : Γ ⊢[PRAAx] pointCN G1 g1) (hg0 : Γ ⊢[PRAAx] pointCN G0 g0)
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z) : Γ ⊢[PRAAx]
    pointCN (lhsF I1 I0 G1 G0 K) (lhsData I1 I0 G1 G0 K i1 i0 g1 g0 z a) :=
  GaussianNamedIncrementDifferenceQuotient.name_regular _ _ K _ _ z a
    (.andI (multiply_fast I1 G1 i1 g1 hi1 hg1) (.andI (multiply_fast I0 G0 i0 g0 hi0 hg0) hk))

theorem rhs_regular (I1 I0 G1 G0 K : PR 2) (i1 i0 g1 g0 z a : PTm n)
    (hi1 : Γ ⊢[PRAAx] pointCN I1 i1) (hi0 : Γ ⊢[PRAAx] pointCN I0 i0)
    (hg1 : Γ ⊢[PRAAx] pointCN G1 g1) (hg0 : Γ ⊢[PRAAx] pointCN G0 g0)
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z) : Γ ⊢[PRAAx]
    pointCN (rhsF I1 I0 G1 G0 K) (rhsData I1 I0 G1 G0 K i1 i0 g1 g0 z a) :=
  add_fast _ _ _ _
    (multiply_fast I1 _ i1 _ hi1
      (GaussianNamedIncrementDifferenceQuotient.name_regular G1 G0 K g1 g0 z a (.andI hg1 (.andI hg0 hk))))
    (multiply_fast G0 _ g0 _ hg0
      (GaussianNamedIncrementDifferenceQuotient.name_regular I1 I0 K i1 i0 z a (.andI hi1 (.andI hi0 hk))))

private def splitF (I1 I0 G1 G0 : PR 2) : PR 2 :=
  addF (multiplyF I1 (DF G1 G0)) (multiplyF G0 (DF I1 I0))

private def splitData (I1 I0 G1 G0 : PR 2) (i1 i0 g1 g0 : PTm n) : PTm n :=
  addData (multiplyData I1 (DF G1 G0) i1 (dd g1 g0)) (multiplyData G0 (DF I1 I0) g0 (dd i1 i0))

private def differenceFactorCost (C F G : PR 2) (c x y : PTm n) : PTm n :=
  (multiplyModulus C (DF F G) c (dd x y)+one)+GaussianNameBounds.U C c*num 6

private def splitBudget (I1 I0 G1 G0 : PR 2) (i1 i0 g1 g0 : PTm n) : PTm n :=
  (num 6+((multiplyModulus I1 G1 i1 g1+one)+(multiplyModulus I0 G0 i0 g0+one)))+
    (three+(differenceFactorCost I1 G1 G0 i1 g1 g0+differenceFactorCost G0 I1 I0 g0 i1 i0))

private theorem difference_factor_error (C F G : PR 2) (c x y p : PTm n)
    (hc : Γ ⊢[PRAAx] pointCN C c)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF C (DF F G)) p (multiplyData C (DF F G) c (dd x y)))
      (qmul (ap2 C p c) (qsub (ap2 F p x) (ap2 G p y))) (differenceFactorCost C F G c x y) (unit p) := by
  have hd := GaussianNamedDifference.name_regular F G x y hf hg
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (multiply_sample_error C (DF F G) c (dd x y) p hc hd)
    (product_right_error _ _ _ _ _ _ _ (unit_positive p)
      (GaussianNamedDifference.sample_error F G x y p hf hg)
      (GaussianNameBounds.sample_bound _ _ p hd) (GaussianNameBounds.sample_bound C c p hc))

private theorem split_at (I1 I0 G1 G0 : PR 2) (i1 i0 g1 g0 p : PTm n)
    (hi1 : Γ ⊢[PRAAx] pointCN I1 i1) (hi0 : Γ ⊢[PRAAx] pointCN I0 i0)
    (hg1 : Γ ⊢[PRAAx] pointCN G1 g1) (hg0 : Γ ⊢[PRAAx] pointCN G0 g0) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (DF (multiplyF I1 G1) (multiplyF I0 G0)) p
        (dd (multiplyData I1 G1 i1 g1) (multiplyData I0 G0 i0 g0)))
      (ap2 (splitF I1 I0 G1 G0) p (splitData I1 I0 G1 G0 i1 i0 g1 g0))
      (splitBudget I1 I0 G1 G0 i1 i0 g1 g0) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have lhs := distance_triangle_same _ _ _ _ _ _ hp
    (GaussianNamedDifference.sample_error (multiplyF I1 G1) (multiplyF I0 G0)
      (multiplyData I1 G1 i1 g1) (multiplyData I0 G0 i0 g0) p
      (multiply_fast I1 G1 i1 g1 hi1 hg1) (multiply_fast I0 G0 i0 g0 hi0 hg0))
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp
      (multiply_sample_error I1 G1 i1 g1 p hi1 hg1) (multiply_sample_error I0 G0 i0 g0 p hi0 hg0))
  have rhs := distance_triangle_same _ _ _ _ _ _ hp
    (add_sample_error (multiplyF I1 (DF G1 G0)) (multiplyF G0 (DF I1 I0))
      (multiplyData I1 (DF G1 G0) i1 (dd g1 g0)) (multiplyData G0 (DF I1 I0) g0 (dd i1 i0)) p
      (multiply_fast _ _ _ _ hi1 (GaussianNamedDifference.name_regular G1 G0 g1 g0 hg1 hg0))
      (multiply_fast _ _ _ _ hg0 (GaussianNamedDifference.name_regular I1 I0 i1 i0 hi1 hi0)))
    (sum_distance _ _ _ _ _ _ _ hp
      (difference_factor_error I1 G1 G0 i1 g1 g0 p hi1 hg1 hg0)
      (difference_factor_error G0 I1 I0 g0 i1 i0 p hg0 hi1 hi0))
  exact GaussianNameRingLaws.through_identity _ _ _ _ _ _ _ hp lhs rhs
    ((qsub_congr (qmul_commutative _ _) (qmul_commutative _ _)).eqTrans
      ((GaussianRationalPowerDifference.product_difference (ap2 G1 p g1) (ap2 G0 p g0) (ap2 I1 p i1) (ap2 I0 p i0)).eqTrans
        (qadd_congr (qmul_commutative _ _) (.eqRefl _))))

private theorem split_cross (I1 I0 G1 G0 : PR 2) (i1 i0 g1 g0 : PTm n)
    (hi1 : Γ ⊢[PRAAx] pointCN I1 i1) (hi0 : Γ ⊢[PRAAx] pointCN I0 i0)
    (hg1 : Γ ⊢[PRAAx] pointCN G1 g1) (hg0 : Γ ⊢[PRAAx] pointCN G0 g0) : Γ ⊢[PRAAx]
    crossEquivalent (DF (multiplyF I1 G1) (multiplyF I0 G0)) (splitF I1 I0 G1 G0)
      (dd (multiplyData I1 G1 i1 g1) (multiplyData I0 G0 i0 g0)) (splitData I1 I0 G1 G0 i1 i0 g1 g0) := by
  apply equivalent_of_envelope _ _ _ _ (splitBudget I1 I0 G1 G0 i1 i0 g1 g0)
    (GaussianNamedDifference.name_regular _ _ _ _
      (multiply_fast I1 G1 i1 g1 hi1 hg1) (multiply_fast I0 G0 i0 g0 hi0 hg0))
    (add_fast _ _ _ _
      (multiply_fast _ _ _ _ hi1 (GaussianNamedDifference.name_regular G1 G0 g1 g0 hg1 hg0))
      (multiply_fast _ _ _ _ hg0 (GaussianNamedDifference.name_regular I1 I0 i1 i0 hi1 hi0)))
  refine .allI ?_
  have shift_regular (F : PR 2) (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN F x) :
      Γ.map Fm.shift ⊢[PRAAx] pointCN F (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hx.shift
  simpa only [splitF,splitData,splitBudget,differenceFactorCost,three,Syn.shift,
    GaussianNameArithmetic.subst_multiplyData,GaussianNameArithmetic.subst_addData,
    GaussianNamedDifference.subst_data,GaussianNameArithmetic.subst_multiplyModulus,
    GaussianNameBounds.subst_U,PTm.subst_add,PTm.subst_mul,LeanProofs.IPRA.PTm.subst_num,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    split_at I1 I0 G1 G0 (Syn.shift i1) (Syn.shift i0) (Syn.shift g1) (Syn.shift g0) (var 0)
      (shift_regular _ _ hi1) (shift_regular _ _ hi0) (shift_regular _ _ hg1) (shift_regular _ _ hg0)

private theorem cancel_increment (K F G : PR 2) (z a x y : PTm n)
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF K F) (multiplyF K G)
      (multiplyData K F z x) (multiplyData K G z y)) : Γ ⊢[PRAAx] crossEquivalent F G x y := by
  let J := GaussianNameReciprocal.nameF K
  let j := GaussianNameReciprocal.nameData a z
  have hj : Γ ⊢[PRAAx] pointCN J j := GaussianNameReciprocal.name_fast K a z hk.andE₁ hk.andE₂
  have unscale (H : PR 2) (u : PTm n) (hu : Γ ⊢[PRAAx] pointCN H u) : Γ ⊢[PRAAx]
      crossEquivalent (multiplyF J (multiplyF K H)) H
        (multiplyData J (multiplyF K H) j (multiplyData K H z u)) u := by
    have cancel := GaussianNameRingLaws.multiply_unit_left (multiplyF J K) H (multiplyData J K j z) u z
      (multiply_fast J K j z hj hk.andE₁) hu (GaussianNameReciprocal.product_one_left K a z hk.andE₁ hk.andE₂)
    exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative J K H j z u hj hk.andE₁ hu)) cancel
  have multiplyBoth := multiply_equivalent J J (multiplyF K F) (multiplyF K G)
    j j (multiplyData K F z x) (multiplyData K G z y) hj hj
    (multiply_fast K F z x hk.andE₁ hf) (multiply_fast K G z y hk.andE₁ hg)
    (cross_to_diagonal _ _ _ _ (cross_refl J j hj)) (cross_to_diagonal _ _ _ _ he)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (unscale F x hf))
    (cross_trans _ _ _ _ _ _ multiplyBoth (unscale G y hg))

theorem product_rule (I1 I0 G1 G0 K : PR 2) (i1 i0 g1 g0 z a : PTm n)
    (hi1 : Γ ⊢[PRAAx] pointCN I1 i1) (hi0 : Γ ⊢[PRAAx] pointCN I0 i0)
    (hg1 : Γ ⊢[PRAAx] pointCN G1 g1) (hg0 : Γ ⊢[PRAAx] pointCN G0 g0)
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z) : Γ ⊢[PRAAx]
    crossEquivalent (lhsF I1 I0 G1 G0 K) (rhsF I1 I0 G1 G0 K)
      (lhsData I1 I0 G1 G0 K i1 i0 g1 g0 z a) (rhsData I1 I0 G1 G0 K i1 i0 g1 g0 z a) := by
  let QG := QF G1 G0 K
  let QI := QF I1 I0 K
  let qg := qd G1 G0 K g1 g0 z a
  let qi := qd I1 I0 K i1 i0 z a
  have hgInput := Prf.andI hg1 (.andI hg0 hk)
  have hiInput := Prf.andI hi1 (.andI hi0 hk)
  have hqg : Γ ⊢[PRAAx] pointCN QG qg := GaussianNamedIncrementDifferenceQuotient.name_regular _ _ _ _ _ _ _ hgInput
  have hqi : Γ ⊢[PRAAx] pointCN QI qi := GaussianNamedIncrementDifferenceQuotient.name_regular _ _ _ _ _ _ _ hiInput
  have reduce_factor (C F G : PR 2) (c x y : PTm n)
      (hc : Γ ⊢[PRAAx] pointCN C c) (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) : Γ ⊢[PRAAx]
      crossEquivalent (multiplyF K (multiplyF C (QF F G K))) (multiplyF C (DF F G))
        (multiplyData K (multiplyF C (QF F G K)) z (multiplyData C (QF F G K) c (qd F G K x y z a)))
        (multiplyData C (DF F G) c (dd x y)) := by
    have hq := GaussianNamedIncrementDifferenceQuotient.name_regular F G K x y z a (.andI hf (.andI hg hk))
    have hd := GaussianNamedDifference.name_regular F G x y hf hg
    have cancel := multiply_equivalent C C (multiplyF K (QF F G K)) (DF F G) c c
      (multiplyData K (QF F G K) z (qd F G K x y z a)) (dd x y) hc hc
      (multiply_fast K _ z _ hk.andE₁ hq) hd (diagonal_refl C c)
      (cross_to_diagonal _ _ _ _
        (GaussianNamedIncrementDifferenceQuotient.left_product F G K x y z a (.andI hf (.andI hg hk))))
    exact cross_trans _ _ _ _ _ _
      (swap_adjacent K C (QF F G K) z c (qd F G K x y z a) hk.andE₁ hc hq) cancel
  have rhsFactors := add_equivalent
    (multiplyF K (multiplyF I1 QG)) (multiplyF I1 (DF G1 G0))
    (multiplyF K (multiplyF G0 QI)) (multiplyF G0 (DF I1 I0))
    (multiplyData K (multiplyF I1 QG) z (multiplyData I1 QG i1 qg))
    (multiplyData I1 (DF G1 G0) i1 (dd g1 g0))
    (multiplyData K (multiplyF G0 QI) z (multiplyData G0 QI g0 qi))
    (multiplyData G0 (DF I1 I0) g0 (dd i1 i0))
    (multiply_fast _ _ _ _ hk.andE₁ (multiply_fast I1 QG i1 qg hi1 hqg))
    (multiply_fast _ _ _ _ hi1 (GaussianNamedDifference.name_regular G1 G0 g1 g0 hg1 hg0))
    (multiply_fast _ _ _ _ hk.andE₁ (multiply_fast G0 QI g0 qi hg0 hqi))
    (multiply_fast _ _ _ _ hg0 (GaussianNamedDifference.name_regular I1 I0 i1 i0 hi1 hi0))
    (cross_to_diagonal _ _ _ _ (reduce_factor I1 G1 G0 i1 g1 g0 hi1 hg1 hg0))
    (cross_to_diagonal _ _ _ _ (reduce_factor G0 I1 I0 g0 i1 i0 hg0 hi1 hi0))
  have rhsScaled := cross_trans _ _ _ _ _ _
    (distributive K (multiplyF I1 QG) (multiplyF G0 QI) z
      (multiplyData I1 QG i1 qg) (multiplyData G0 QI g0 qi) hk.andE₁
      (multiply_fast I1 QG i1 qg hi1 hqg) (multiply_fast G0 QI g0 qi hg0 hqi)) rhsFactors
  have lhsScaled := GaussianNamedIncrementDifferenceQuotient.left_product
    (multiplyF I1 G1) (multiplyF I0 G0) K (multiplyData I1 G1 i1 g1) (multiplyData I0 G0 i0 g0) z a
    (.andI (multiply_fast I1 G1 i1 g1 hi1 hg1) (.andI (multiply_fast I0 G0 i0 g0 hi0 hg0) hk))
  exact cancel_increment K _ _ z a _ _ hk
    (lhs_regular I1 I0 G1 G0 K i1 i0 g1 g0 z a hi1 hi0 hg1 hg0 hk)
    (rhs_regular I1 I0 G1 G0 K i1 i0 g1 g0 z a hi1 hi0 hg1 hg0 hk)
    (cross_trans _ _ _ _ _ _ lhsScaled
      (cross_trans _ _ _ _ _ _ (split_cross I1 I0 G1 G0 i1 i0 g1 g0 hi1 hi0 hg1 hg0)
        (cross_symm _ _ _ _ rhsScaled)))

/-- The exact product split also applies to the original quotient by a
rational Gaussian increment, with the same literal reciprocal in every quotient. -/
theorem native_product_rule (I1 I0 G1 G0 : PR 2) (i1 i0 g1 g0 h B : PTm n)
    (hi1 : Γ ⊢[PRAAx] pointCN I1 i1) (hi0 : Γ ⊢[PRAAx] pointCN I0 i0)
    (hg1 : Γ ⊢[PRAAx] pointCN G1 g1) (hg0 : Γ ⊢[PRAAx] pointCN G0 g0) :
    Γ ⊢[PRAAx] crossEquivalent
      (GaussianNamedDifferenceQuotient.nameF (multiplyF I1 G1) (multiplyF I0 G0))
      (addF (multiplyF I1 (GaussianNamedDifferenceQuotient.nameF G1 G0))
        (multiplyF G0 (GaussianNamedDifferenceQuotient.nameF I1 I0)))
      (GaussianNamedDifferenceQuotient.data (multiplyF I1 G1) (multiplyF I0 G0)
        (multiplyData I1 G1 i1 g1) (multiplyData I0 G0 i0 g0) h B)
      (addData (multiplyData I1 (GaussianNamedDifferenceQuotient.nameF G1 G0) i1
          (GaussianNamedDifferenceQuotient.data G1 G0 g1 g0 h B))
        (multiplyData G0 (GaussianNamedDifferenceQuotient.nameF I1 I0) g0
          (GaussianNamedDifferenceQuotient.data I1 I0 i1 i0 h B))) := by
  let C := GaussianBoundedConstantProductName.constantF
  let c := GaussianNamedDifferenceQuotient.inverse h B
  let QG := DF G1 G0
  let QI := DF I1 I0
  let x := dd g1 g0
  let y := dd i1 i0
  let F := multiplyF I1 QG
  let G := multiplyF G0 QI
  let a := multiplyData I1 QG i1 x
  let b := multiplyData G0 QI g0 y
  have hc := GaussianBoundedConstantProductName.constant_regular (Γ := Γ) c
  have hx := GaussianNamedDifference.name_regular G1 G0 g1 g0 hg1 hg0
  have hy := GaussianNamedDifference.name_regular I1 I0 i1 i0 hi1 hi0
  have ha := multiply_fast I1 QG i1 x hi1 hx
  have hb := multiply_fast G0 QI g0 y hg0 hy
  have hs := split_cross I1 I0 G1 G0 i1 i0 g1 g0 hi1 hi0 hg1 hg0
  have hd := GaussianNamedDifference.name_regular (multiplyF I1 G1) (multiplyF I0 G0)
    (multiplyData I1 G1 i1 g1) (multiplyData I0 G0 i0 g0)
    (multiply_fast I1 G1 i1 g1 hi1 hg1) (multiply_fast I0 G0 i0 g0 hi0 hg0)
  have leading := GaussianGammaAdjacentCutoff.multiply_cross C C _ (addF F G) c c _ (addData a b)
    hc hc hd (add_fast F G a b ha hb) (cross_refl C c hc) hs
  have distrib := distributive C F G c a b hc ha hb
  have swap := GaussianNamedGammaHalfShift.add_cross
    (multiplyF C F) (multiplyF I1 (multiplyF C QG))
    (multiplyF C G) (multiplyF G0 (multiplyF C QI))
    (multiplyData C F c a) (multiplyData I1 (multiplyF C QG) i1 (multiplyData C QG c x))
    (multiplyData C G c b) (multiplyData G0 (multiplyF C QI) g0 (multiplyData C QI c y))
    (multiply_fast C F c a hc ha) (multiply_fast _ _ _ _ hi1 (multiply_fast C QG c x hc hx))
    (multiply_fast C G c b hc hb) (multiply_fast _ _ _ _ hg0 (multiply_fast C QI c y hc hy))
    (swap_adjacent C I1 QG c i1 x hc hi1 hx) (swap_adjacent C G0 QI c g0 y hc hg0 hy)
  exact cross_trans _ _ _ _ _ _ leading (cross_trans _ _ _ _ _ _ distrib swap)


theorem actual_named_increment_product_rule_closed (I1 I0 G1 G0 K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((pointCN I1 (var 0) ⋏ (pointCN I0 (var 1) ⋏ (pointCN G1 (var 2) ⋏
        (pointCN G0 (var 3) ⋏ GaussianNameReciprocal.input K (var 5) (var 4))))) ⟶
        crossEquivalent (lhsF I1 I0 G1 G0 K) (rhsF I1 I0 G1 G0 K)
          (lhsData I1 I0 G1 G0 K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (rhsData I1 I0 G1 G0 K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (product_rule I1 I0 G1 G0 K _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedIncrementProductRule
