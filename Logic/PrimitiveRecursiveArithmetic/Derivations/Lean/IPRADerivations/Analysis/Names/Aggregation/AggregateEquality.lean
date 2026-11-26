import IPRADerivations.Analysis.Geometry.Distances.RationalHausdorffTriangle
import IPRADerivations.Analysis.Inequalities.GapRemoval
import IPRADerivations.Core.CommonLemmas

/-!
# Equality of regular rational aggregate names

Finite-demand Section 3, equation (E). The fixed PR list evaluators have
internal numerical parameters and precision indices. Covers use the original
independently denominated rational coordinates, via the actual Hausdorff code.

Four finite covers give `H(S_k,U_k) ≤ 2/2^k + 6/2^v`. A single explicit
precision `v = 6*2^k*D(S_k,U_k)` removes the auxiliary error by integer
discreteness. No limiting argument or decidability of name equality is used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.AggregateEquality

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalHausdorff
open LeanProofs.IPRA.Analysis.RationalHausdorffTriangle
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def unit (k : PTm n) : PTm n := pw two k

@[simp] theorem subst_unit {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (unit k) = unit (Syn.subst σ k) := by simp [unit]

theorem unit_positive (k : PTm n) : Γ ⊢[PRAAx] le one (unit k) :=
  le_congr (.eqRefl _) (DiophantineNumberTheory.FLTMultiples.pw_pos one k).eqSymm
    ((succ_monus_succ zero _).eqTrans (zero_le _))

private alias positive_cancel := Common.mul_cancel_le

theorem close_radius_congr (S T d : PTm n) {A A' B B' : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] originalClose S T d A B) :
    Γ ⊢[PRAAx] originalClose S T d A' B' :=
  .andI (originalCover_radius_congr S T d hA hB (Prf.andE₁ h))
    (originalCover_radius_congr T S d hA hB (Prf.andE₂ h))

theorem close_scale (S T d A B c : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] originalClose S T d A B) :
    Γ ⊢[PRAAx] originalClose S T d (c*A) (c*B) :=
  original_close_of_bound S T d _ _ hS hT
    (le_congr (by ipra_ring) (by ipra_ring)
      (le_mul_mono (le_refl c) (bound_of_original_close S T d A B h)))

/-- Addition at an explicitly proved positive common radius denominator. -/
theorem close_add (S T U d A C B : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hU : Γ ⊢[PRAAx] le one (length U))
    (hB : Γ ⊢[PRAAx] le one B)
    (hST : Γ ⊢[PRAAx] originalClose S T d A B)
    (hTU : Γ ⊢[PRAAx] originalClose T U d C B) :
    Γ ⊢[PRAAx] originalClose S U d (A+C) B := by
  have composed := originalClose_triangle S T U d A B C B hST hTU
  have bound := bound_of_original_close S U d _ _ composed
  exact original_close_of_bound S U d _ _ hS hU
    (positive_cancel hB (le_congr (by ipra_ring) (by ipra_ring) bound))

def sample (S : PR 2) (k x : PTm n) : PTm n := ap2 S k x

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (S : PR 2) (k x : PTm n) :
    Syn.subst σ (sample S k x) = sample S (Syn.subst σ k) (Syn.subst σ x) := by simp [sample]

def nonempty (S : PR 2) (x : PTm n) : Fm PTm n :=
  .all (le one (length (sample S (var 0) (Syn.shift x))))

def regular (S : PR 2) (d x : PTm n) : Fm PTm n :=
  .all (.all (originalClose (sample S (var 1) (Syn.shift (Syn.shift x)))
    (sample S (var 0) (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift d))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

/-- Unbounded name equality, rather than a test on PR program indices. -/
def equivalent (S T : PR 2) (d x : PTm n) : Fm PTm n :=
  .all (originalClose (sample S (var 0) (Syn.shift x)) (sample T (var 0) (Syn.shift x))
    (Syn.shift d) two (unit (var 0)))

@[simp] theorem subst_nonempty {m : ℕ} (σ : Fin n → PTm m) (S : PR 2) (x : PTm n) :
    (nonempty S x).subst σ = nonempty S (Syn.subst σ x) := by
  simp only [nonempty, Fm.subst_all, subst_le, Foundations.SequenceComposition.subst_length, subst_sample, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_shift, Syn.shift_subst, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

@[simp] theorem subst_regular {m : ℕ} (σ : Fin n → PTm m) (S : PR 2) (d x : PTm n) :
    (regular S d x).subst σ = regular S (Syn.subst σ d) (Syn.subst σ x) := by
  simp only [regular, Fm.subst_all, subst_originalClose, subst_sample, subst_unit, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_shift, Syn.shift_subst, Syn.shift_var, Fin.succ_zero_eq_one]

@[simp] theorem subst_equivalent {m : ℕ} (σ : Fin n → PTm m) (S T : PR 2) (d x : PTm n) :
    (equivalent S T d x).subst σ = equivalent S T (Syn.subst σ d) (Syn.subst σ x) := by
  simp only [equivalent, Fm.subst_all, subst_originalClose, subst_sample, subst_unit, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_shift, Syn.shift_subst, two, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem nonempty_at (S : PR 2) (k x : PTm n) (h : Γ ⊢[PRAAx] nonempty S x) :
    Γ ⊢[PRAAx] le one (length (sample S k x)) := by
  simpa [nonempty] using Prf.allE k h

theorem regular_at (S : PR 2) (j k d x : PTm n) (h : Γ ⊢[PRAAx] regular S d x) :
    Γ ⊢[PRAAx] originalClose (sample S j x) (sample S k x) d
      (unit j+unit k) (unit j*unit k) := by
  have a : Γ ⊢[PRAAx] .all (originalClose (sample S (Syn.shift j) (Syn.shift x))
      (sample S (var 0) (Syn.shift x)) (Syn.shift d)
      (unit (Syn.shift j)+unit (var 0)) (unit (Syn.shift j)*unit (var 0))) := by
    simpa only [regular, Fm.subst_all, subst_originalClose, subst_sample, subst_unit,
      PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ,
      subst_up_shift', Syn.inst_zero, Syn.inst_succ, Syn.subst_inst_shift, Syn.shift_var] using Prf.allE j h
  simpa only [Fm.subst_all, subst_originalClose, subst_sample, subst_unit,
    PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_succ,
    Syn.subst_inst_shift] using Prf.allE k a

theorem equivalent_at (S T : PR 2) (k d x : PTm n) (h : Γ ⊢[PRAAx] equivalent S T d x) :
    Γ ⊢[PRAAx] originalClose (sample S k x) (sample T k x) d two (unit k) := by
  simpa [equivalent] using Prf.allE k h

/-- The source's exact finite comparison `2 e_k + 6 e_v`, with no assumption
that either intermediate aggregate has a chosen infinite point. -/
theorem four_cover_bound (S T U : PR 2) (k v d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hT : Γ ⊢[PRAAx] nonempty T x)
    (hU : Γ ⊢[PRAAx] nonempty U x)
    (rS : Γ ⊢[PRAAx] regular S d x) (rU : Γ ⊢[PRAAx] regular U d x)
    (hST : Γ ⊢[PRAAx] equivalent S T d x) (hTU : Γ ⊢[PRAAx] equivalent T U d x) :
    Γ ⊢[PRAAx] originalClose (sample S k x) (sample U k x) d
      (two*unit v+num 6*unit k) (unit k*unit v) := by
  have hB : Γ ⊢[PRAAx] le one (unit k*unit v) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (unit_positive k) (unit_positive v))
  have first := regular_at S k v d x rS
  have second := close_scale _ _ d two (unit v) (unit k)
    (nonempty_at S v x hS) (nonempty_at T v x hT) (equivalent_at S T v d x hST)
  have third := close_scale _ _ d two (unit v) (unit k)
    (nonempty_at T v x hT) (nonempty_at U v x hU) (equivalent_at T U v d x hTU)
  have fourth := close_radius_congr _ _ d (add_comm _ _) (mul_comm _ _) (regular_at U v k d x rU)
  have a := close_add _ _ _ d _ _ _ (nonempty_at S k x hS) (nonempty_at T v x hT) hB first second
  have b := close_add _ _ _ d _ _ _ (nonempty_at S k x hS) (nonempty_at U v x hU) hB a third
  have c := close_add _ _ _ d _ _ _ (nonempty_at S k x hS) (nonempty_at U k x hU) hB b fourth
  exact close_radius_congr _ _ d (by ipra_ring) (.eqRefl _) c

theorem equivalent_transitive_at (S T U : PR 2) (k d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hT : Γ ⊢[PRAAx] nonempty T x)
    (hU : Γ ⊢[PRAAx] nonempty U x)
    (rS : Γ ⊢[PRAAx] regular S d x) (rU : Γ ⊢[PRAAx] regular U d x)
    (hST : Γ ⊢[PRAAx] equivalent S T d x) (hTU : Γ ⊢[PRAAx] equivalent T U d x) :
    Γ ⊢[PRAAx] originalClose (sample S k x) (sample U k x) d two (unit k) := by
  let C := num 6*unit k*denominator (sample S k x) (sample U k x) d
  have bound := bound_of_original_close _ _ d _ _ (four_cover_bound S T U k C d x hS hT hU rS rU hST hTU)
  have reduced : Γ ⊢[PRAAx] le
      ((unit k*numerator (sample S k x) (sample U k x) d)*unit C)
      ((two*denominator (sample S k x) (sample U k x) d)*unit C+C) :=
    le_congr (by ipra_ring) (by dsimp [C]; ipra_ring) bound
  exact original_close_of_bound _ _ d two (unit k)
    (nonempty_at S k x hS) (nonempty_at U k x hU) (GapRemoval.gap reduced)

theorem equivalent_transitive (S T U : PR 2) (d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hT : Γ ⊢[PRAAx] nonempty T x)
    (hU : Γ ⊢[PRAAx] nonempty U x)
    (rS : Γ ⊢[PRAAx] regular S d x) (rU : Γ ⊢[PRAAx] regular U d x)
    (hST : Γ ⊢[PRAAx] equivalent S T d x) (hTU : Γ ⊢[PRAAx] equivalent T U d x) :
    Γ ⊢[PRAAx] equivalent S U d x := by
  refine .allI ?_
  exact equivalent_transitive_at S T U (var 0) (Syn.shift d) (Syn.shift x)
    (by simpa only [Fm.shift, subst_nonempty, subst_regular, subst_equivalent, Syn.shift] using hS.shift) (by simpa only [Fm.shift, subst_nonempty, subst_regular, subst_equivalent, Syn.shift] using hT.shift)
    (by simpa only [Fm.shift, subst_nonempty, subst_regular, subst_equivalent, Syn.shift] using hU.shift) (by simpa only [Fm.shift, subst_nonempty, subst_regular, subst_equivalent, Syn.shift] using rS.shift)
    (by simpa only [Fm.shift, subst_nonempty, subst_regular, subst_equivalent, Syn.shift] using rU.shift) (by simpa only [Fm.shift, subst_nonempty, subst_regular, subst_equivalent, Syn.shift] using hST.shift)
    (by simpa only [Fm.shift, subst_nonempty, subst_regular, subst_equivalent, Syn.shift] using hTU.shift)

theorem equivalent_symmetric (S T : PR 2) (d x : PTm n)
    (h : Γ ⊢[PRAAx] equivalent S T d x) : Γ ⊢[PRAAx] equivalent T S d x := by
  refine .allI ?_
  have shifted : Γ.map Fm.shift ⊢[PRAAx] equivalent S T (Syn.shift d) (Syn.shift x) := by
    simpa only [Fm.shift, subst_nonempty, subst_regular, subst_equivalent, Syn.shift] using h.shift
  have current := equivalent_at S T (var 0) (Syn.shift d) (Syn.shift x) shifted
  exact Prf.andI (Prf.andE₂ current) (Prf.andE₁ current)

theorem pointRadius_diagonal (z d A B : PTm n) :
    Γ ⊢[PRAAx] pointRadius z z d A B := by
  refine .allI (.impI ?_)
  have cross : (lt (var 0) (Syn.shift d) :: Γ.map Fm.shift) ⊢[PRAAx]
      Foundations.GapDecision.zabs (crossNumerator (Syn.shift z) (Syn.shift z) (var 0)) ≐ zero := by
    refine (Foundations.GapDecision.zabs_congr (v := ZT.ofNat zero) ?_).eqTrans ?_
    · simp only [crossNumerator, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_zero, map_zero]
      ring
    · exact (congrAdd (monus_self zero) (monus_self zero)).eqTrans (zero_add zero)
  exact le_congr ((congrMul (.eqRefl _) cross).eqTrans (mul_zero _)).eqSymm
    (.eqRefl _) (zero_le _)

theorem close_diagonal (S d A B : PTm n) : Γ ⊢[PRAAx] originalClose S S d A B := by
  have cover : Γ ⊢[PRAAx] originalCover .left .right S S d A B := by
    refine .allI (.impI ?_)
    exact originalHit_intro .left .right (Syn.shift S) (Syn.shift S) (Syn.shift d)
      (Syn.shift A) (Syn.shift B) (var 0) (var 0) Prf.hyp0
      (pointRadius_diagonal _ _ _ _)
  exact .andI cover cover

theorem equivalent_reflexive (S : PR 2) (d x : PTm n) :
    Γ ⊢[PRAAx] equivalent S S d x :=
  .allI (close_diagonal _ _ _ _)

theorem equivalent_transitive_closed (S T U : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (nonempty S (var 1) ⟶ nonempty T (var 1) ⟶ nonempty U (var 1) ⟶
        regular S (var 0) (var 1) ⟶ regular U (var 0) (var 1) ⟶
        equivalent S T (var 0) (var 1) ⟶ equivalent T U (var 0) (var 1) ⟶
        equivalent S U (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (.impI (.impI (.impI (.impI (.impI
    (equivalent_transitive S T U _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))))

theorem equivalent_symmetric_closed (S T : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (equivalent S T (var 0) (var 1) ⟶ equivalent T S (var 0) (var 1)) :=
  closeUniv 2 (.impI (equivalent_symmetric S T _ _ Prf.hyp0))

theorem equivalent_reflexive_closed (S : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (equivalent S S (var 0) (var 1)) :=
  closeUniv 2 (equivalent_reflexive S _ _)

end LeanProofs.IPRA.Analysis.AggregateEquality
