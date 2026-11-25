import IPRADerivations.Analysis.GaussianArctangentSlope
import IPRADerivations.Core.Search

/-!
# Exact finite crossing of an arctangent grid target

In the common factorial denominator, a target is a natural number.
The first index at or above that target has a non-strict upper row
and strictly lower preceding rows. The search uses only the literal
finite totals and ordinary natural arithmetic.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentGridSearch

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentExponentialPrefix (source total subst_total)
open BaselQuadrature (Qb)
open Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def testBody : PTm 2 :=
  monus (fstT (var 1)) (total (var 0) (fstT (sndT (var 1))) (sndT (sndT (var 1))))

private def searchData (T M L : PTm n) : PTm n := pairT T (pairT M L)

def crossing (T M L : PTm n) : PTm n := Search.mu testBody (succ M) (searchData T M L)

private theorem test_at (i T M L : PTm n) :
    Γ ⊢[PRAAx] inst2 testBody i (searchData T M L) ≐ monus T (total i M L) := by
  let x := searchData T M L
  have hT : Γ ⊢[PRAAx] fstT x ≐ T := fst_pair _ _
  have hM : Γ ⊢[PRAAx] fstT (sndT x) ≐ M := (congrFst (snd_pair T (pairT M L))).eqTrans (fst_pair _ _)
  have hL : Γ ⊢[PRAAx] sndT (sndT x) ≐ L := (congrSnd (snd_pair T (pairT M L))).eqTrans (snd_pair _ _)
  simpa [testBody,inst2,x] using Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (monus (var 0) (total (var 1) (var 2) (var 3)) : PTm 4)
    (σ := ![fstT x,i,fstT (sndT x),sndT (sndT x)]) (σ' := ![T,i,M,L])
    (fun j => by fin_cases j; exact hT; exact .eqRefl _; exact hM; exact hL)

theorem crossing_spec (i T M L : PTm n) (hT : Γ ⊢[PRAAx] le T (total M M L)) :
    Γ ⊢[PRAAx] le (crossing T M L) M ⋏
      (le T (total (crossing T M L) M L) ⋏ (lt i (crossing T M L) ⟶ lt (total i M L) T)) := by
  let x := searchData T M L
  have last : Γ ⊢[PRAAx] inst2 testBody M x ≐ zero := (test_at M T M L).eqTrans hT
  have found := Search.search_found (f := testBody) (N := succ M) last (le_refl (succ M))
  refine .andI found.andE₂.andE₂ (.andI ((test_at _ T M L).eqSymm.eqTrans found.andE₂.andE₁) (.impI ?_))
  have hi : lt i (crossing T M L) :: Γ ⊢[PRAAx] lt i (crossing T M L) := Prf.hyp0
  have hm := Search.search_minimal (f := testBody) (N := succ M) (x := x) hi
  refine .orE (lt_or_le (total i M L) T) Prf.hyp0 ?_
  exact .botE _ (.impE hm.wk ((test_at i T M L).eqTrans Prf.hyp0))

theorem crossing_residual (T M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hT : Γ ⊢[PRAAx] le T (total M M L)) :
    Γ ⊢[PRAAx] le (M*total (crossing T M L) M L) (M*T+fact L) := by
  let k := crossing T M L
  refine .orE (zero_or_succ k) ?_ ?_
  · have e : Γ ⊢[PRAAx] total zero M L ≐ zero := sum_zero Qb (pairT M L)
    have atZero : (k ≐ zero)::Γ ⊢[PRAAx] total k M L ≐ zero :=
      (congrAp2 (sumF Qb) Prf.hyp0 (.eqRefl _)).eqTrans e.wk
    exact le_congr ((congrMul (.eqRefl M) atZero).eqTrans (mul_zero M)).eqSymm (.eqRefl _) (zero_le _)
  · let j := pred k
    have hk : (k ≐ succ j)::Γ ⊢[PRAAx] k ≐ succ j := Prf.hyp0
    have hj : (k ≐ succ j)::Γ ⊢[PRAAx] lt j k :=
      le_congr (.eqRefl _) hk.eqSymm (le_refl (succ j))
    have e := (succ_eq_add_one j).eqSymm.eqTrans hk.eqSymm
    have h := crossing_spec (Γ := (k ≐ succ j)::Γ) j T M L hT.wk
    have admissible := le_congr e.eqSymm (.eqRefl _) h.andE₁
    have row := (GaussianArctangentSlope.finite_slope j one M L hs.wk admissible).andE₂
    have lo := le_of_lt (.impE h.andE₂.andE₂ hj)
    have mono := add_le_add_right (fact L) (le_mul_mono (le_refl M) lo)
    have ee := congrMul (.eqRefl M) (congrAp2 (sumF Qb) e (.eqRefl (pairT M L)))
    exact le_trans (le_congr ee (congrAdd (.eqRefl _) (one_mul (fact L))) row) mono

theorem actual_arctangent_grid_crossing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 1) (total (var 2) (var 2) (var 3)) ⟶ le (crossing (var 1) (var 2) (var 3)) (var 2) ⋏
      (le (var 1) (total (crossing (var 1) (var 2) (var 3)) (var 2) (var 3)) ⋏
        (lt (var 0) (crossing (var 1) (var 2) (var 3)) ⟶ lt (total (var 0) (var 2) (var 3)) (var 1)))) :=
  closeUniv 4 (.impI (crossing_spec _ _ _ _ Prf.hyp0))

theorem actual_arctangent_grid_crossing_residual_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 1) (var 2) ⟶ le (var 0) (total (var 1) (var 1) (var 2)) ⟶
      le (var 1*total (crossing (var 0) (var 1) (var 2)) (var 1) (var 2)) (var 1*var 0+fact (var 2))) :=
  closeUniv 3 (.impI (.impI (crossing_residual _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentGridSearch
