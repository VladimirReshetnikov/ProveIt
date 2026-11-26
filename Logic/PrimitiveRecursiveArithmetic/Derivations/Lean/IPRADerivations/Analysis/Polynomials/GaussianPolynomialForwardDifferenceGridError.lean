import IPRADerivations.Analysis.Polynomials.GaussianPolynomialForwardDifferenceGrid
import IPRADerivations.Analysis.Names.GaussianNamedDifference
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Uniform error of the original Gaussian forward-difference grid

One adjacent-subtraction row doubles a uniform input error. Bounded
formula induction propagates this estimate to each actual stage and
the terminal value at internally encoded degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open GaussianNamedDifference (difference_distance)
open GaussianPolynomialForwardDifferenceGrid (adjacent adjacent_lookup grid grid_zero grid_succ value)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded boundedSyntax bounded_formula qsub)
open GaussianRationalTranslationStages (remaining remaining_step)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowBound (V W L A B : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift L) ⟶
  distanceBounded (entry (Syn.shift V) (var 0)) (entry (Syn.shift W) (var 0)) (Syn.shift A) (Syn.shift B))

@[simp] theorem subst_rowBound {l : ℕ} (σ : Fin n → PTm l) (V W L A B : PTm n) :
    (rowBound V W L A B).subst σ = rowBound (Syn.subst σ V) (Syn.subst σ W) (Syn.subst σ L)
      (Syn.subst σ A) (Syn.subst σ B) := by simp [rowBound,Syn.subst_shift,Syn.shift_subst]

theorem row_at (V W L A B i : PTm n) (hrow : Γ ⊢[PRAAx] rowBound V W L A B) (hi : Γ ⊢[PRAAx] lt i L) :
    Γ ⊢[PRAAx] distanceBounded (entry V i) (entry W i) A B := by
  have h : Γ ⊢[PRAAx] lt i L ⟶ distanceBounded (entry V i) (entry W i) A B := by
    simpa [rowBound] using hrow.allE i
  exact .impE h hi

private theorem row_congr {V W L A B X Y M C : PTm n} (hV : Γ ⊢[PRAAx] V ≐ X) (hW : Γ ⊢[PRAAx] W ≐ Y)
    (hL : Γ ⊢[PRAAx] L ≐ M) (hA : Γ ⊢[PRAAx] A ≐ C) (h : Γ ⊢[PRAAx] rowBound V W L A B) :
    Γ ⊢[PRAAx] rowBound X Y M C B := by
  have e := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (rowBound (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
    ![V,W,L,A,B] ![X,Y,M,C,B] (by intro i; fin_cases i; exact hV; exact hW; exact hL; exact hA; exact .eqRefl _)
    (by simpa using h)
  simpa using e

theorem adjacent_bound (V W L A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] rowBound V W (succ L) A B) :
    Γ ⊢[PRAAx] rowBound (adjacent V L) (adjacent W L) L (A+A) B := by
  refine .allI (.impI ?_)
  let a (t : PTm n) := Syn.shift t
  let Δ := lt (var 0) (a L) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hb : Δ ⊢[PRAAx] le one (a B) := by simpa [Δ,a,one,Fm.shift,Syn.shift] using hB.shift.wk
  have old : Δ ⊢[PRAAx] rowBound (a V) (a W) (succ (a L)) (a A) (a B) := by
    simpa [Δ,a,Fm.shift,Syn.shift] using h.shift.wk
  have hi : Δ ⊢[PRAAx] lt i (a L) := Prf.hyp0
  have hn : Δ ⊢[PRAAx] lt (succ i) (succ (a L)) := (succ_monus_succ _ _).eqTrans hi
  have now := row_at (a V) (a W) (succ (a L)) (a A) (a B) i old (lt_of_lt_of_le hi (le_succ_self _))
  have next := row_at (a V) (a W) (succ (a L)) (a A) (a B) (succ i) old hn
  have combined := difference_distance _ _ _ _ _ _ _ hb next now
  simpa [rowBound,Δ,a,i,Syn.shift] using
    distance_congr (adjacent_lookup (a V) (a L) i hi).eqSymm (adjacent_lookup (a W) (a L) i hi).eqSymm
      (.eqRefl _) (.eqRefl _) combined

private def stageLaw (V W N A B j : PTm n) : Fm PTm n :=
  le j N ⟶ rowBound (grid V N j) (grid W N j) (succ (remaining N j)) (pw two j*A) B

private def stageSyntax (V W N A B j : PTm n) : BFm n := .imp (.le j N) (.all (succ (remaining N j))
  (boundedSyntax (qsub (entry (Syn.shift (grid V N j)) (var 0)) (entry (Syn.shift (grid W N j)) (var 0)))
    (Syn.shift (pw two j*A)) (Syn.shift B)))

private theorem stage_formula (V W N A B j : PTm n) : formula (stageSyntax V W N A B j) = stageLaw V W N A B j := by
  simp only [stageSyntax,formula,stageLaw,rowBound,bounded_formula,GaussianRationalMetric.distanceBounded,BFm.le,le]

@[simp] private theorem subst_stageLaw {l : ℕ} (σ : Fin n → PTm l) (V W N A B j : PTm n) :
    (stageLaw V W N A B j).subst σ = stageLaw (Syn.subst σ V) (Syn.subst σ W) (Syn.subst σ N) (Syn.subst σ A)
      (Syn.subst σ B) (Syn.subst σ j) := by simp [stageLaw,pw,two,one]

theorem stage_bound (V W N A B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] rowBound V W (succ N) A B)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    rowBound (grid V N j) (grid W N j) (succ (remaining N j)) (pw two j*A) B := by
  let a (t : PTm n) := Syn.shift t
  let S := stageSyntax (a V) (a W) (a N) (a A) (a B) (var 0)
  have h0 : Γ ⊢[PRAAx] (formula S).subst (Syn.inst zero) := by
    simp only [S,a,stage_formula,subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
    have radius := (congrMul (pw_zero (Γ := Γ) two) (.eqRefl A)).eqTrans (one_mul A)
    exact .impI (row_congr (grid_zero V N).eqSymm (grid_zero W N).eqSymm (congrSucc (monus_zero N).eqSymm) radius.eqSymm h).wk
  have hs : formula S :: Γ.map Fm.shift ⊢[PRAAx] (formula S).subst (repl (succ (var 0))) := by
    simp only [S,a,stage_formula,subst_stageLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
    refine .impI ?_
    let Δ := le (succ (var 0)) (a N) :: stageLaw (a V) (a W) (a N) (a A) (a B) (var 0) :: Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    let L := remaining (a N) i
    let C := pw two i*a A
    have hb : Δ ⊢[PRAAx] le one (a B) := by simpa [Δ,a,one,Fm.shift,Syn.shift] using hB.shift.wk.wk
    have step : Δ ⊢[PRAAx] lt i (a N) := Prf.hyp0
    have old : Δ ⊢[PRAAx] rowBound (grid (a V) (a N) i) (grid (a W) (a N) i) (succ L) C (a B) :=
      .impE Prf.hyp1 (le_trans (le_succ_self _) step)
    have actual := adjacent_bound _ _ L C (a B) hb old
    have radius : Δ ⊢[PRAAx] C+C ≐ pw two (succ i)*a A :=
      (by dsimp only [C]; ipra_ring : Δ ⊢[PRAAx] C+C ≐ (pw two i*two)*a A).eqTrans
        (congrMul (pw_succ two i).eqSymm (.eqRefl _))
    exact row_congr (grid_succ _ _ _).eqSymm (grid_succ _ _ _).eqSymm (remaining_step _ _ step) radius actual
  have current : Γ ⊢[PRAAx] stageLaw V W N A B j := by
    simpa only [S,a,stage_formula,subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Foundations.BoundedSyntaxInduction.induction_at S j h0 hs
  exact .impE current hj

theorem terminal_bound (V W N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] rowBound V W (succ N) A B) :
    Γ ⊢[PRAAx] distanceBounded (value V N) (value W N) (pw two N*A) B :=
  row_at _ _ _ _ _ zero (stage_bound V W N A B N hB h (le_refl _)) (zero_lt_succ _)

theorem actual_Gaussian_grid_forward_difference_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 4) ⋏ rowBound (var 0) (var 1) (succ (var 2)) (var 3) (var 4)) ⟶
      distanceBounded (value (var 0) (var 2)) (value (var 1) (var 2)) (pw two (var 2)*var 3) (var 4)) :=
  closeUniv 5 (.impI (terminal_bound _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridError
