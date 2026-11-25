import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.Powers

/-!
# Bounded products

Product counterparts of the sum tools of `Core/SumLemmas`, for `∏_{i<N} f(i, x)`:

* `prod_congr_bounded`: products agree when the bodies agree below the bound (the parameters may
  differ);
* `prod_one`: `∏_{i<N} 1 = 1`;
* `prod_const_of`: if `h(i, y) = C` for `i < N`, then `∏_{i<N} h(i, y) = C^N`;
* `prod_pos_bounded`: a product of positive factors is positive;
* `prod_zero_of`: a zero factor below the bound makes the product zero;
* `pos_of_eq_succ`, `pos_mul'`: positivity helpers (`a > 0` is written `a = succ (pred a)`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Positivity helpers -/

theorem pos_of_eq_succ {a c : PTm n} (h : Γ ⊢[PRAAx] a ≐ succ c) : Γ ⊢[PRAAx] a ≐ succ (pred a) :=
  h.eqTrans (congrSucc ((congrPred h).eqTrans (pred_succ c)).eqSymm)

theorem pos_mul' {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] a * b ≐ succ (pred (a * b)) :=
  pos_of_eq_succ (c := pred a * pred b + pred a + pred b)
    ((congrMul ha hb).eqTrans (by ipra_ring))

/-! ## Congruence -/

/-- Products agree when the bodies agree below the bound (with possibly different parameters). -/
theorem prod_congr_bounded (f g : PTm 2) (x y N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 f (var 0) (Syn.shift x) ≐ inst2 g (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] ap2 (prodF f) N x ≐ ap2 (prodF g) N y := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      (ap2 (prodF f) (var 0) (Syn.shift x) ≐ ap2 (prodF g) (var 0) (Syn.shift y))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simpa using .impI ((prod_zero (Γ := le zero N :: Γ) f x).eqTrans (prod_zero _ _).eqSymm)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      have hf := h.allOpen
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ (ap2 (prodF f) (var 0) (Syn.shift x) ≐ ap2 (prodF g) (var 0) (Syn.shift y))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      refine (prod_succ f (var 0) _).eqTrans (.eqTrans ?_ (prod_succ g (var 0) _).eqSymm)
      exact congrMul (.impE Prf.hyp1 hle) (.impE hf.wk.wk Prf.hyp0)
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-! ## Constant products -/

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev prodOneF : Fm PTm 2 := ap2 (prodF (one : PTm 2)) (var 0) (var 1) ≐ one

private theorem prod_one₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] prodOneF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact prod_zero _ _
  · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine (prod_succ _ _ _).eqTrans ?_
    have e : Syn.subst (![var 0, var 1] : Fin 2 → PTm 2) (one : PTm 2) = one := by simp
    rw [e]
    exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)

/-- `∏_{i<N} 1 = 1`. -/
theorem prod_one (N x : PTm n) : Γ ⊢[PRAAx] ap2 (prodF (one : PTm 2)) N x ≐ one := by
  have h := inst (Γ := Γ) prod_one₀ (![N, x] : Fin 2 → PTm n)
  simpa using h

/-- If `h(i, y) = C` for `i < N`, then `∏_{i<N} h(i, y) = C^N`. -/
theorem prod_const_of (h : PTm 2) (N C y : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst2 h (var 0) (Syn.shift y) ≐ Syn.shift C))) :
    Γ ⊢[PRAAx] ap2 (prodF h) N y ≐ pw C N := by
  refine prod_congr_bounded h (var 1) y C N (.allI (.impI ?_))
  have e : inst2 (var 1 : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift C) = Syn.shift C := by simp [inst2]
  rw [e]
  exact Prf.impE hp.allOpen.wk Prf.hyp0

/-! ## Positivity -/

/-- A product of positive factors is positive. -/
theorem prod_pos_bounded (f : PTm 2) (x N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 f (var 0) (Syn.shift x) ≐ succ (pred (inst2 f (var 0) (Syn.shift x)))))) :
    Γ ⊢[PRAAx] ap2 (prodF f) N x ≐ succ (pred (ap2 (prodF f) N x)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      (ap2 (prodF f) (var 0) (Syn.shift x) ≐ succ (pred (ap2 (prodF f) (var 0) (Syn.shift x))))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_pred, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (pos_of_eq_succ (prod_zero f x))
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_pred, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have hf := h.allOpen
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶
            (ap2 (prodF f) (var 0) (Syn.shift x) ≐ succ (pred (ap2 (prodF f) (var 0) (Syn.shift x))))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      have hm := pos_mul' (.impE Prf.hyp1 hle) (.impE hf.wk.wk Prf.hyp0)
      exact pos_of_eq_succ ((prod_succ f (var 0) _).eqTrans hm)
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_pred, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 (le_refl N)

/-! ## A zero factor -/

theorem zero_step (f : PTm 2) {N i x : PTm n}
    (ih : Γ ⊢[PRAAx] lt i N ⟶ ((inst2 f i x ≐ zero) ⟶ (ap2 (prodF f) N x ≐ zero))) :
    Γ ⊢[PRAAx] lt i (succ N) ⟶ ((inst2 f i x ≐ zero) ⟶ (ap2 (prodF f) (succ N) x ≐ zero)) := by
  refine .impI (.impI (.orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp1)) ?_ ?_))
  · exact (prod_succ f N x).eqTrans
      ((congrMul (Prf.impE (Prf.impE ih.wk.wk.wk Prf.hyp0) Prf.hyp1) (.eqRefl _)).eqTrans (zero_mul _))
  · exact (prod_succ f N x).eqTrans
      ((congrMul (.eqRefl _) ((congrInst2 f Prf.hyp0.eqSymm (.eqRefl _)).eqTrans Prf.hyp1)).eqTrans (mul_zero _))

/-- Variables: `0 = N`, `1 = i`, `2 = x`. -/
private abbrev prodZeroF (f : PTm 2) : Fm PTm 3 :=
  lt (var 1) (var 0) ⟶ ((inst2 f (var 1) (var 2) ≐ zero) ⟶ (ap2 (prodF f) (var 0) (var 2) ≐ zero))

private theorem prod_zero_of₀ (f : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] prodZeroF f := by
  refine ind _ ⟨lt_QF _ _, ⟨trivial, trivial⟩⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (lt_zero_absurd _ Prf.hyp0)
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, subst_inst2, Syn.subst_var, Syn.repl_zero,
      repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact zero_step f Prf.hyp0

/-- A zero factor below the bound makes the product zero. -/
theorem prod_zero_of (f : PTm 2) {N i x : PTm n} (hi : Γ ⊢[PRAAx] lt i N)
    (hf : Γ ⊢[PRAAx] inst2 f i x ≐ zero) : Γ ⊢[PRAAx] ap2 (prodF f) N x ≐ zero := by
  have h := inst (Γ := Γ) (prod_zero_of₀ f) (![N, i, x] : Fin 3 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, subst_inst2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact Prf.impE (Prf.impE h hi) hf

end LeanProofs.IPRA
