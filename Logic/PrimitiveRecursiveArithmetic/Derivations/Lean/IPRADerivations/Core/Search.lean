import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Signum

/-!
# Bounded search in iPRA

For a body `f(i, x)`, `μ(N, x)` is the least `i < N` with `f(i, x) = 0`, and `N` if
there is none. It is defined by primitive recursion on `N`:
`μ(0, x) = 0`, `μ(N + 1, x) = μ(N, x) + eqb(μ(N, x), N) · sg(f(N, x))`.
Derived, with `i` and `x` free:

* `search_spec`: `μ ≤ N`, `μ < N → f(μ, x) = 0`, and `i < μ → f(i, x) ≠ 0`
  (one joint induction on `N`);
* `search_found`: `f(i, x) = 0 → i < N → μ < N ∧ f(μ, x) = 0 ∧ μ ≤ i`;
* `search_minimal`: `i < μ → f(i, x) ≠ 0`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

namespace Search

variable (f : PTm 2)

/-- The step; variables `0 = N`, `1 = μ(N, x)`, `2 = x`. -/
abbrev muStep : PTm 3 := var 1 + eqb (var 1) (var 0) * sg (inst2 f (var 0) (var 2))
abbrev muF : PR 2 := rec2 zero (muStep f)
/-- `μ(N, x)`. -/
abbrev mu (N x : PTm n) : PTm n := ap2 (muF f) N x

variable {f}

theorem mu_zero (x : PTm n) : Γ ⊢[PRAAx] mu f zero x ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero (muStep f) x

theorem mu_succ (N x : PTm n) :
    Γ ⊢[PRAAx] mu f (succ N) x ≐ mu f N x + eqb (mu f N x) N * sg (inst2 f N x) := by
  have h := rec2_succ (Γ := Γ) zero (muStep f) N x
  simp only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_eqb, subst_inst2,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at h
  exact h

/-- The invariant; variables `0 = N`, `1 = i`, `2 = x`. -/
abbrev specF : Fm PTm 3 :=
  le (mu f (var 0) (var 2)) (var 0) ⋏
    ((lt (mu f (var 0) (var 2)) (var 0) ⟶ (inst2 f (mu f (var 0) (var 2)) (var 2) ≐ zero)) ⋏
      (lt (var 1) (mu f (var 0) (var 2)) ⟶ neg (inst2 f (var 1) (var 2) ≐ zero)))

private abbrev M : PTm 3 := mu f (var 0) (var 2)
private abbrev M' : PTm 3 := mu f (succ (var 0)) (var 2)

theorem spec_open : ([] : List (Fm PTm 3)) ⊢[PRAAx] specF (f := f) := by
  ipra_ind (⟨le_QF _ _, ⟨lt_QF _ _, trivial⟩, lt_QF _ _, trivial, trivial⟩) [subst_le, subst_lt, subst_neg,
      subst_ap2, subst_inst2]
  · have h0 := mu_zero (f := f) (Γ := ([] : List (Fm PTm 2))) (var 1)
    refine .andI (le_congr h0.eqSymm (.eqRefl _) (le_refl _)) (.andI ?_ ?_)
    · exact .impI (lt_zero_absurd _ (lt_congr h0.wk (.eqRefl _) Prf.hyp0))
    · exact .impI (lt_zero_absurd _ (lt_congr (.eqRefl _) h0.wk Prf.hyp0))
  · have hle : [specF (f := f)] ⊢[PRAAx] le (M (f := f)) (var 0) := .andE₁ Prf.hyp0
    have hfound : [specF (f := f)] ⊢[PRAAx]
        lt (M (f := f)) (var 0) ⟶ (inst2 f (M (f := f)) (var 2) ≐ zero) := .andE₁ (.andE₂ Prf.hyp0)
    have hmin : [specF (f := f)] ⊢[PRAAx]
        lt (var 1) (M (f := f)) ⟶ neg (inst2 f (var 1) (var 2) ≐ zero) := .andE₂ (.andE₂ Prf.hyp0)
    have hs := mu_succ (f := f) (Γ := [specF (f := f)]) (var 0) (var 2)
    refine .orE (lt_or_eq_of_le hle) ?_ ?_
    · -- Found before N: μ' = μ.
      have hne : (lt (M (f := f)) (var 0) :: [specF (f := f)]) ⊢[PRAAx] neg (M (f := f) ≐ var 0) :=
        .impI (lt_irrefl (var 0) _ (lt_congr Prf.hyp0 (.eqRefl _) Prf.hyp1))
      have e : (lt (M (f := f)) (var 0) :: [specF (f := f)]) ⊢[PRAAx] M' (f := f) ≐ M (f := f) :=
        hs.wk.eqTrans ((congrAdd (.eqRefl _) ((congrMul (eqb_of_ne hne) (.eqRefl _)).eqTrans
          (zero_mul _))).eqTrans (add_zero _))
      refine .andI (le_congr e.eqSymm (.eqRefl _) (le_trans (le_of_lt Prf.hyp0) (le_succ_self _)))
        (.andI ?_ ?_)
      · exact .impI ((congrInst2 f e.wk (.eqRefl _)).eqTrans (.impE hfound.wk.wk Prf.hyp1))
      · exact .impI (.impE hmin.wk.wk (lt_congr (.eqRefl _) e.wk Prf.hyp0))
    · -- Not found before N: μ = N.
      have hM : ((M (f := f) ≐ var 0) :: [specF (f := f)]) ⊢[PRAAx] M (f := f) ≐ var 0 := Prf.hyp0
      refine .orE (zero_or_succ (inst2 f (var 0) (var 2))) ?_ ?_
      · -- f(N) = 0: μ' = N.
        have e : ((inst2 f (var 0) (var 2) ≐ zero) :: (M (f := f) ≐ var 0) :: [specF (f := f)]) ⊢[PRAAx]
            M' (f := f) ≐ var 0 := by
          refine hs.wk.wk.eqTrans ((congrAdd hM.wk ((congrMul (.eqRefl _) ((congrMonus (.eqRefl _)
            (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero)).eqTrans (mul_zero _))).eqTrans
            (add_zero _))
        refine .andI (le_congr e.eqSymm (.eqRefl _) (le_succ_self _)) (.andI ?_ ?_)
        · exact .impI ((congrInst2 f e.wk (.eqRefl _)).eqTrans Prf.hyp1)
        · exact .impI (.impE hmin.wk.wk.wk (lt_congr (.eqRefl _) (e.wk.eqTrans hM.wk.wk.eqSymm) Prf.hyp0))
      · -- f(N) ≠ 0: μ' = N + 1.
        have e : ((inst2 f (var 0) (var 2) ≐ succ (pred (inst2 f (var 0) (var 2)))) ::
            (M (f := f) ≐ var 0) :: [specF (f := f)]) ⊢[PRAAx] M' (f := f) ≐ succ (var 0) := by
          refine hs.wk.wk.eqTrans ((congrAdd hM.wk ((congrMul (eqb_of_eq hM.wk) ((congrMonus (.eqRefl _)
            (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans (sg_succ _))).eqTrans (one_mul _))).eqTrans
            (succ_eq_add_one _).eqSymm)
        refine .andI (le_congr e.eqSymm (.eqRefl _) (le_refl _)) (.andI ?_ ?_)
        · exact .impI (lt_irrefl (succ (var 0)) _ (lt_congr e.wk (.eqRefl _) Prf.hyp0))
        · refine .impI (.orE (lt_succ_cases (lt_congr (.eqRefl _) e.wk Prf.hyp0)) ?_ ?_)
          · exact .impE hmin.wk.wk.wk.wk (lt_congr (.eqRefl _) hM.wk.wk.wk.eqSymm Prf.hyp0)
          · refine .impI (succ_ne_zero (a := pred (inst2 f (var 0) (var 2))) ?_)
            refine (Prf.hyp (φ := inst2 f (var 0) (var 2) ≐ succ (pred (inst2 f (var 0) (var 2))))
              (by simp)).eqSymm.eqTrans ?_
            exact (congrInst2 f Prf.hyp1.eqSymm (.eqRefl _)).eqTrans Prf.hyp0

/-- `μ ≤ N`, `μ < N → f(μ, x) = 0`, and `i < μ → f(i, x) ≠ 0`. -/
theorem search_spec (N i x : PTm n) :
    Γ ⊢[PRAAx] le (mu f N x) N ⋏ ((lt (mu f N x) N ⟶ (inst2 f (mu f N x) x ≐ zero)) ⋏
      (lt i (mu f N x) ⟶ neg (inst2 f i x ≐ zero))) := by
  have h := inst (Γ := Γ) (spec_open (f := f)) (![N, i, x] : Fin 3 → PTm n)
  simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_le, subst_lt, subst_neg, subst_ap2,
    subst_inst2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem search_minimal {N i x : PTm n} (h : Γ ⊢[PRAAx] lt i (mu f N x)) :
    Γ ⊢[PRAAx] neg (inst2 f i x ≐ zero) :=
  .impE (Prf.andE₂ (Prf.andE₂ (search_spec N i x))) h

/-- A zero below `N` is found, at or before it. -/
theorem search_found {N i x : PTm n} (hf : Γ ⊢[PRAAx] inst2 f i x ≐ zero) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] lt (mu f N x) N ⋏ ((inst2 f (mu f N x) x ≐ zero) ⋏ le (mu f N x) i) := by
  have s := search_spec (Γ := Γ) (f := f) N i x
  -- μ ≤ i, since i < μ would contradict f(i) = 0.
  have hmi : Γ ⊢[PRAAx] le (mu f N x) i := by
    refine .orE (lt_or_le i (mu f N x)) ?_ Prf.hyp0
    exact .botE _ (.impE (.impE (Prf.andE₂ (Prf.andE₂ s)).wk Prf.hyp0) hf.wk)
  have hlt : Γ ⊢[PRAAx] lt (mu f N x) N := lt_of_le_of_lt hmi hi
  exact .andI hlt (.andI (.impE (Prf.andE₁ (Prf.andE₂ s)) hlt) hmi)

end Search

end LeanProofs.IPRA
