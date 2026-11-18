import IPRADerivations.Analysis.GaussianGeneralPolynomialValueName
import IPRADerivations.Analysis.GaussianRationalPowerDifference

/-!
# Euclidean equivalence and zero transport for actual Gaussian names

Two fixed PR2 observation programs retain separate numerical data. Their
source diagonal comparison is 2*epsilon_m. Genuine fast-name contracts
upgrade it to the exact two-precision comparison by removing a dyadic
slack from each fixed original rational difference. The equivalence laws
and zero-predicate transport use the same finite integer-gap theorem.
No completed field, code equality, selector, or quantified induction is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNameEquivalence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded qsub)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN point_cn_at)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialValueName (programZero program_zero_at)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder
  (distance_congr distance_symmetric distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def diagonalEquivalent (f g : PR 2) (x y : PTm n) : Fm PTm n := .all
  (distanceBounded (ap2 f (var 0) (Syn.shift x)) (ap2 g (var 0) (Syn.shift y)) two (unit (var 0)))

def crossEquivalent (f g : PR 2) (x y : PTm n) : Fm PTm n := .all (.all
  (distanceBounded (ap2 f (var 1) (Syn.shift (Syn.shift x)))
    (ap2 g (var 0) (Syn.shift (Syn.shift y)))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

@[simp] theorem subst_diagonalEquivalent {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y : PTm n) :
    (diagonalEquivalent f g x y).subst σ = diagonalEquivalent f g (Syn.subst σ x) (Syn.subst σ y) := by
  simp [diagonalEquivalent,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_crossEquivalent {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (x y : PTm n) :
    (crossEquivalent f g x y).subst σ = crossEquivalent f g (Syn.subst σ x) (Syn.subst σ y) := by
  simp [crossEquivalent,Syn.subst_shift,Syn.shift_subst]

theorem diagonal_at (f g : PR 2) (x y m : PTm n)
    (h : Γ ⊢[PRAAx] diagonalEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f m x) (ap2 g m y) two (unit m) := by
  simpa [diagonalEquivalent] using h.allE m

theorem cross_at (f g : PR 2) (x y s t : PTm n)
    (h : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f s x) (ap2 g t y) (unit s+unit t) (unit s*unit t) := by
  have pair : Γ ⊢[PRAAx] .all
      (distanceBounded (ap2 f (Syn.shift s) (Syn.shift x)) (ap2 g (var 0) (Syn.shift y))
        (unit (Syn.shift s)+unit (var 0)) (unit (Syn.shift s)*unit (var 0))) := by
    simpa only [crossEquivalent,Fm.subst_all,GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_unit,
      PTm.subst_add,PTm.subst_mul,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,
      Foundations.BoundedFormulas.subst_up_shift',Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,
      Syn.shift_var] using h.allE s
  simpa only [GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_unit,PTm.subst_add,PTm.subst_mul,
    Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using pair.allE t

theorem point_at (f : PR 2) (x s t : PTm n) (hF : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f s x) (ap2 f t x) (unit s+unit t) (unit s*unit t) := by
  simpa only [GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using point_cn_at f x s t hF

/-- The genuine three-leg comparison has exactly four dyadic errors at
its auxiliary precision. The two requested observations remain fixed. -/
theorem diagonal_slack (f g : PR 2) (x y s t m : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN f x) (hG : Γ ⊢[PRAAx] pointCN g y)
    (hEq : Γ ⊢[PRAAx] diagonalEquivalent f g x y) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 f s x) (ap2 g t y))
      (unit s+unit t) (unit s*unit t) (two*two) m := by
  have sm := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive m)
  have mt := positive_product (Γ := Γ) _ _ (unit_positive m) (unit_positive t)
  have first := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ sm (unit_positive m)
    (point_at f x s m hF) (diagonal_at f g x y m hEq)
  have combined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _
    (positive_product _ _ sm (unit_positive m)) mt first (point_at g y m t hG)
  change Γ ⊢[PRAAx] distanceBounded (ap2 f s x) (ap2 g t y)
    ((unit s+unit t)*unit m+(two*two)*(unit s*unit t)) ((unit s*unit t)*unit m)
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ sm (unit_positive m)) mt)
    (positive_product _ _ (positive_product _ _ (unit_positive s) (unit_positive t)) (unit_positive m))
    (le_of_eq_add (d := zero) (by ipra_ring)) combined

/-- A finite integer-gap query removes the auxiliary precision; no limit
or induction on the two universal name predicates is needed. -/
theorem diagonal_cross_at (f g : PR 2) (x y s t : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN f x) (hG : Γ ⊢[PRAAx] pointCN g y)
    (hEq : Γ ⊢[PRAAx] diagonalEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f s x) (ap2 g t y) (unit s+unit t) (unit s*unit t) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (two*two)
    (positive_product _ _ (unit_positive s) (unit_positive t))
  refine .allI ?_
  have hf : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hF.shift
  have hg : Γ.map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift y) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hG.shift
  have he : Γ.map Fm.shift ⊢[PRAAx] diagonalEquivalent f g (Syn.shift x) (Syn.shift y) := by
    simpa only [Fm.shift,subst_diagonalEquivalent,Syn.shift] using hEq.shift
  simpa only [Syn.shift,subst_ap2,GaussianRationalMetric.subst_qsub,subst_unit,PTm.subst_add,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    diagonal_slack f g (Syn.shift x) (Syn.shift y) (Syn.shift s) (Syn.shift t) (var 0) hf hg he

theorem diagonal_to_cross (f g : PR 2) (x y : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN f x) (hG : Γ ⊢[PRAAx] pointCN g y)
    (hEq : Γ ⊢[PRAAx] diagonalEquivalent f g x y) : Γ ⊢[PRAAx] crossEquivalent f g x y := by
  refine .allI (.allI ?_)
  have hf : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hF.shift.shift
  have hg : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hG.shift.shift
  have he : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      diagonalEquivalent f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,subst_diagonalEquivalent,Syn.shift] using hEq.shift.shift
  exact diagonal_cross_at f g _ _ (var 1) (var 0) hf hg he

theorem cross_to_diagonal (f g : PR 2) (x y : PTm n)
    (hEq : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx] diagonalEquivalent f g x y := by
  refine .allI ?_
  have he : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent f g (Syn.shift x) (Syn.shift y) := by
    simpa only [Fm.shift,subst_crossEquivalent,Syn.shift] using hEq.shift
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive (var 0)) (unit_positive (var 0))) (unit_positive (var 0))
    (le_of_eq_add (d := zero) (by ipra_ring)) (cross_at f g _ _ (var 0) (var 0) he)

theorem diagonal_iff_cross (f g : PR 2) (x y : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN f x) (hG : Γ ⊢[PRAAx] pointCN g y) : Γ ⊢[PRAAx]
    Fm.iff (diagonalEquivalent f g x y) (crossEquivalent f g x y) :=
  .andI (.impI (diagonal_to_cross f g x y hF.wk hG.wk Prf.hyp0))
    (.impI (cross_to_diagonal f g x y Prf.hyp0))

/-! The diagonal relation is reflexive even on raw streams. Its transitive
law below is restricted to genuine fast names. -/

theorem diagonal_refl (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx] diagonalEquivalent f f x x := by
  refine .allI ?_
  exact distance_radius_mono _ _ zero (unit (var 0)) two (unit (var 0))
    (unit_positive _) (unit_positive _) (le_of_eq_add (d := two*unit (var 0)) (by ipra_ring))
    (GaussianRationalPowerDifference.distance_refl_zero _ _ (unit_positive _))

theorem cross_refl (f : PR 2) (x : PTm n) (hF : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent f f x x := hF

theorem diagonal_symm (f g : PR 2) (x y : PTm n)
    (hEq : Γ ⊢[PRAAx] diagonalEquivalent f g x y) : Γ ⊢[PRAAx] diagonalEquivalent g f y x := by
  refine .allI ?_
  have he : Γ.map Fm.shift ⊢[PRAAx] diagonalEquivalent f g (Syn.shift x) (Syn.shift y) := by
    simpa only [Fm.shift,subst_diagonalEquivalent,Syn.shift] using hEq.shift
  exact distance_symmetric _ _ _ _ (unit_positive _) (diagonal_at f g _ _ (var 0) he)

theorem cross_symm (f g : PR 2) (x y : PTm n)
    (hEq : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx] crossEquivalent g f y x := by
  refine .allI (.allI ?_)
  have he : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      crossEquivalent f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,subst_crossEquivalent,Syn.shift] using hEq.shift.shift
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
      (cross_at f g _ _ (var 0) (var 1) he))

/-- An intermediate observation contributes two errors at its precision. -/
theorem cross_trans_slack (f g h : PR 2) (x y z s t m : PTm n)
    (hFG : Γ ⊢[PRAAx] crossEquivalent f g x y) (hGH : Γ ⊢[PRAAx] crossEquivalent g h y z) :
    Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack (qsub (ap2 f s x) (ap2 h t z))
      (unit s+unit t) (unit s*unit t) two m := by
  have sm := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive m)
  have mt := positive_product (Γ := Γ) _ _ (unit_positive m) (unit_positive t)
  have result := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ sm mt
    (cross_at f g x y s m hFG) (cross_at g h y z m t hGH)
  change Γ ⊢[PRAAx] distanceBounded (ap2 f s x) (ap2 h t z)
    ((unit s+unit t)*unit m+two*(unit s*unit t)) ((unit s*unit t)*unit m)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ sm mt)
    (positive_product _ _ (positive_product _ _ (unit_positive s) (unit_positive t)) (unit_positive m))
    (le_of_eq_add (d := zero) (by ipra_ring)) result

theorem cross_trans_at (f g h : PR 2) (x y z s t : PTm n)
    (hFG : Γ ⊢[PRAAx] crossEquivalent f g x y) (hGH : Γ ⊢[PRAAx] crossEquivalent g h y z) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f s x) (ap2 h t z) (unit s+unit t) (unit s*unit t) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ two
    (positive_product _ _ (unit_positive s) (unit_positive t))
  refine .allI ?_
  have fg : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent f g (Syn.shift x) (Syn.shift y) := by
    simpa only [Fm.shift,subst_crossEquivalent,Syn.shift] using hFG.shift
  have gh : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent g h (Syn.shift y) (Syn.shift z) := by
    simpa only [Fm.shift,subst_crossEquivalent,Syn.shift] using hGH.shift
  simpa only [Syn.shift,subst_ap2,GaussianRationalMetric.subst_qsub,subst_unit,PTm.subst_add,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    cross_trans_slack f g h (Syn.shift x) (Syn.shift y) (Syn.shift z) (Syn.shift s) (Syn.shift t) (var 0) fg gh

theorem cross_trans (f g h : PR 2) (x y z : PTm n)
    (hFG : Γ ⊢[PRAAx] crossEquivalent f g x y) (hGH : Γ ⊢[PRAAx] crossEquivalent g h y z) :
    Γ ⊢[PRAAx] crossEquivalent f h x z := by
  refine .allI (.allI ?_)
  have fg : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      crossEquivalent f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,subst_crossEquivalent,Syn.shift] using hFG.shift.shift
  have gh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      crossEquivalent g h (Syn.shift (Syn.shift y)) (Syn.shift (Syn.shift z)) := by
    simpa only [Fm.shift,subst_crossEquivalent,Syn.shift] using hGH.shift.shift
  exact cross_trans_at f g h _ _ _ (var 1) (var 0) fg gh

theorem diagonal_trans (f g h : PR 2) (x y z : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN f x) (hG : Γ ⊢[PRAAx] pointCN g y) (hH : Γ ⊢[PRAAx] pointCN h z)
    (hFG : Γ ⊢[PRAAx] diagonalEquivalent f g x y) (hGH : Γ ⊢[PRAAx] diagonalEquivalent g h y z) :
    Γ ⊢[PRAAx] diagonalEquivalent f h x z :=
  cross_to_diagonal f h x z (cross_trans f g h x y z
    (diagonal_to_cross f g x y hF hG hFG) (diagonal_to_cross g h y z hG hH hGH))

/-! Zero is the existing predicate on the ACTUAL returned program, not a
semantic equality to a point in an assumed completion. -/

theorem cross_zero_slack (f g : PR 2) (x y k m : PTm n)
    (hEq : Γ ⊢[PRAAx] crossEquivalent f g x y) (hZero : Γ ⊢[PRAAx] programZero f x) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (ap2 g k y) one (unit k) two m := by
  have mk := positive_product (Γ := Γ) _ _ (unit_positive m) (unit_positive k)
  have compared := distance_symmetric _ _ _ _ mk (cross_at f g x y m k hEq)
  have result := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ mk (unit_positive m)
    compared (program_zero_at f x m hZero)
  change Γ ⊢[PRAAx] bounded (ap2 g k y) (one*unit m+two*unit k) (unit k*unit m)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ mk (unit_positive m)) (positive_product _ _ (unit_positive k) (unit_positive m))
    (le_of_eq_add (d := zero) (by ipra_ring)) result

theorem cross_zero_at (f g : PR 2) (x y k : PTm n)
    (hEq : Γ ⊢[PRAAx] crossEquivalent f g x y) (hZero : Γ ⊢[PRAAx] programZero f x) : Γ ⊢[PRAAx]
    bounded (ap2 g k y) one (unit k) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ two (unit_positive k)
  refine .allI ?_
  have he : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent f g (Syn.shift x) (Syn.shift y) := by
    simpa only [Fm.shift,subst_crossEquivalent,Syn.shift] using hEq.shift
  have hz : Γ.map Fm.shift ⊢[PRAAx] programZero f (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralPolynomialValueName.subst_programZero,Syn.shift] using hZero.shift
  simpa only [Syn.shift,subst_ap2,subst_unit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    cross_zero_slack f g (Syn.shift x) (Syn.shift y) (Syn.shift k) (var 0) he hz

theorem cross_zero_transport (f g : PR 2) (x y : PTm n)
    (hEq : Γ ⊢[PRAAx] crossEquivalent f g x y) (hZero : Γ ⊢[PRAAx] programZero f x) : Γ ⊢[PRAAx]
    programZero g y := by
  refine .allI ?_
  have he : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent f g (Syn.shift x) (Syn.shift y) := by
    simpa only [Fm.shift,subst_crossEquivalent,Syn.shift] using hEq.shift
  have hz : Γ.map Fm.shift ⊢[PRAAx] programZero f (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralPolynomialValueName.subst_programZero,Syn.shift] using hZero.shift
  exact cross_zero_at f g _ _ (var 0) he hz

theorem cross_zero_iff (f g : PR 2) (x y : PTm n)
    (hEq : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    Fm.iff (programZero f x) (programZero g y) :=
  .andI (.impI (cross_zero_transport f g x y hEq.wk Prf.hyp0))
    (.impI (cross_zero_transport g f y x (cross_symm f g x y hEq).wk Prf.hyp0))

theorem zero_transport (f g : PR 2) (x y : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN f x) (hG : Γ ⊢[PRAAx] pointCN g y)
    (hEq : Γ ⊢[PRAAx] diagonalEquivalent f g x y) (hZero : Γ ⊢[PRAAx] programZero f x) : Γ ⊢[PRAAx]
    programZero g y := cross_zero_transport f g x y (diagonal_to_cross f g x y hF hG hEq) hZero

theorem zero_iff (f g : PR 2) (x y : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN f x) (hG : Γ ⊢[PRAAx] pointCN g y)
    (hEq : Γ ⊢[PRAAx] diagonalEquivalent f g x y) : Γ ⊢[PRAAx]
    Fm.iff (programZero f x) (programZero g y) :=
  cross_zero_iff f g x y (diagonal_to_cross f g x y hF hG hEq)

/-! Closed contracts keep all persistent data numerical. The only external
parameters are the fixed observation programs. -/

theorem proper_diagonal_cross_equivalence_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN f (var 0) ⟶ pointCN g (var 1) ⟶
      Fm.iff (diagonalEquivalent f g (var 0) (var 1)) (crossEquivalent f g (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (diagonal_iff_cross f g _ _ Prf.hyp1 Prf.hyp0)))

theorem diagonal_reflexivity_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (diagonalEquivalent f f (var 0) (var 0)) := closeUniv 1 (diagonal_refl f _)

theorem proper_cross_reflexivity_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ crossEquivalent f f (var 0) (var 0)) :=
  closeUniv 1 (.impI (cross_refl f _ Prf.hyp0))

theorem diagonal_symmetry_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (diagonalEquivalent f g (var 0) (var 1) ⟶ diagonalEquivalent g f (var 1) (var 0)) :=
  closeUniv 2 (.impI (diagonal_symm f g _ _ Prf.hyp0))

theorem cross_symmetry_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent f g (var 0) (var 1) ⟶ crossEquivalent g f (var 1) (var 0)) :=
  closeUniv 2 (.impI (cross_symm f g _ _ Prf.hyp0))

theorem cross_transitivity_closed (f g h : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (crossEquivalent f g (var 0) (var 1) ⟶ crossEquivalent g h (var 1) (var 2) ⟶
      crossEquivalent f h (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (cross_trans f g h _ _ _ Prf.hyp1 Prf.hyp0)))

theorem proper_diagonal_transitivity_closed (f g h : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((pointCN f (var 0) ⋏ (pointCN g (var 1) ⋏ pointCN h (var 2))) ⟶
      diagonalEquivalent f g (var 0) (var 1) ⟶ diagonalEquivalent g h (var 1) (var 2) ⟶
      diagonalEquivalent f h (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (diagonal_trans f g h _ _ _
    (.andE₁ hyp2) (.andE₁ (.andE₂ hyp2)) (.andE₂ (.andE₂ hyp2)) Prf.hyp1 Prf.hyp0))))

theorem cross_equivalent_program_zero_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent f g (var 0) (var 1) ⟶ Fm.iff (programZero f (var 0)) (programZero g (var 1))) :=
  closeUniv 2 (.impI (cross_zero_iff f g _ _ Prf.hyp0))

theorem proper_diagonal_program_zero_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((pointCN f (var 0) ⋏ pointCN g (var 1)) ⟶ diagonalEquivalent f g (var 0) (var 1) ⟶
      Fm.iff (programZero f (var 0)) (programZero g (var 1))) :=
  closeUniv 2 (.impI (.impI (zero_iff f g _ _ (.andE₁ Prf.hyp1) (.andE₂ Prf.hyp1) Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNameEquivalence
