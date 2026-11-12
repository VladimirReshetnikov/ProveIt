import ConciseIPRA.NativeModels

/-!
# No fixed point of the successor without the progress rule

Seven of the eight rules of the kernel are independent (`NativeModels`).  For
the eighth, `Q` by progress, a countermodel must have nonstandard numbers.
This module formalizes one constraint on such a model that was so far an
argument on paper: it has no fixed point of the successor.

* `NoInd.no_succ_fixed`: the kernel **without** `Q` by progress derives
  `0 = 1` from `S c = c`, for every term `c`.

The derivation uses no induction.  Let `zf y = sel(y, 1, 0)` be the zero
test, `nz y = sel(y, 0, 1)` its complement and
`P(a, b) = sel(a, nz b, zf b)`.  Three equations hold at every term, each by
cases on a number, with the base and the step proved by computation:

  `zf (zf y) = nz y`,   `P(zf y, nz y) = 1`,   `P(a, a) = 0`.

Now let `v = I(c, 0; u. zf u)`.  The second computation equation gives
`I(S c, 0; u. zf u) = zf v`, and `S c = c` gives `I(S c, 0; u. zf u) = v`, so
`v = zf v`.  Hence `zf v = zf (zf v) = nz v`, and
`1 = P(zf v, nz v) = P(zf v, zf v) = 0`.

The same argument with a counter modulo `k` excludes cycles of length `k`;
that is not formalized.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n : ℕ}

/-- The seven rules other than `Q` by progress. -/
def Rules.noInd : Rules := ⟨true, true, true, true, true, true, true, false⟩

namespace NoInd

/-- Derivability in the kernel without `Q` by progress. -/
abbrev K (Γ : List (NFm n)) (A : NFm n) : Prop := FPrf Rules.noInd Γ A

variable {Γ : List (NFm n)}

theorem refl (t : Tm n) : K Γ (.eq t t) :=
  .trOne rfl (Syn.var 0) (.iterZero rfl t (Syn.var 0)) (.iterZero rfl t (Syn.var 0))

theorem symm {s t : Tm n} (h : K Γ (.eq s t)) : K Γ (.eq t s) :=
  .trOne rfl (Syn.var 0) (refl s) h

theorem trans {s t u : Tm n} (h₁ : K Γ (.eq s t)) (h₂ : K Γ (.eq t u)) : K Γ (.eq s u) :=
  .trOne rfl (Syn.var 0) h₂ (symm h₁)

theorem congr (h : Tm (n + 1)) {s t : Tm n} (e : K Γ (.eq s t)) :
    K Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) :=
  .trOne rfl h e (refl _)

theorem selZero (a b : Tm n) : K Γ (.eq (Tm.sel zero a b) a) := .iterZero rfl a _

theorem selSucc (c a b : Tm n) : K Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := FPrf.iterSucc (r := Rules.noInd) (Γ := Γ) rfl c a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

theorem selCongr {c c' : Tm n} (a b : Tm n) (e : K Γ (.eq c c')) :
    K Γ (.eq (Tm.sel c a b) (Tm.sel c' a b)) := by
  have h := congr (Tm.sel (Syn.var 0) (Syn.shift a) (Syn.shift b)) e
  simpa only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h

/-- Cases on a number: an equation in one variable that holds at `0` and at
every successor, in every context, holds at every term. -/
theorem cases (a b : Tm (n + 1)) (t : Tm n)
    (h0 : ∀ Δ : List (NFm n), K Δ (.eq (Syn.subst (inst zero) a) (Syn.subst (inst zero) b)))
    (hS : ∀ Δ : List (NFm (n + 1)), K Δ (.eq (Syn.subst (repl (succ (Syn.var 0))) a)
      (Syn.subst (repl (succ (Syn.var 0))) b))) :
    K Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) := by
  have hD : K Γ (.D ((NFm.eq a b).subst (up (fun i => Syn.var i.succ)))) := by
    refine .dICase rfl _ zero ?_
    rw [NFm.subst_dummy_inst]
    exact hS _
  have hQ : K Γ (.Q (.eq a b)) := by
    refine .dE rfl hD ?_
    show K (.Q ((NFm.eq a b).subst (up (fun i => Syn.var i.succ))) :: Γ.map NFm.shift)
      (.Q ((NFm.eq a b).subst (up (fun i => Syn.var i.succ))))
    exact .hyp rfl List.mem_cons_self
  exact .qE rfl t hQ (h0 _)

/-- `zf (zf y) = nz y`. -/
theorem zf_zf (t : Tm n) :
    K Γ (.eq (Tm.sel (Tm.sel t (succ zero) zero) (succ zero) zero)
      (Tm.sel t zero (succ zero))) := by
  have k := cases (Γ := Γ) (Tm.sel (Tm.sel (Syn.var 0) (succ zero) zero) (succ zero) zero)
    (Tm.sel (Syn.var 0) zero (succ zero)) t
    (fun Δ => by
      simp only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_succ, Tm.subst_zero]
      exact trans (selCongr _ _ (selZero _ _)) (trans (selSucc _ _ _) (symm (selZero _ _))))
    (fun Δ => by
      simp only [Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Tm.subst_succ, Tm.subst_zero]
      exact trans (selCongr _ _ (selSucc _ _ _)) (trans (selZero _ _) (symm (selSucc _ _ _))))
  simpa only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_succ, Tm.subst_zero] using k

/-- `P(a, a) = 0`. -/
theorem p_diag (t : Tm n) :
    K Γ (.eq (Tm.sel t (Tm.sel t zero (succ zero)) (Tm.sel t (succ zero) zero)) zero) := by
  have k := cases (Γ := Γ)
    (Tm.sel (Syn.var 0) (Tm.sel (Syn.var 0) zero (succ zero))
      (Tm.sel (Syn.var 0) (succ zero) zero)) zero t
    (fun Δ => by
      simp only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_succ, Tm.subst_zero]
      exact trans (selZero _ _) (selZero _ _))
    (fun Δ => by
      simp only [Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Tm.subst_succ, Tm.subst_zero]
      exact trans (selSucc _ _ _) (selSucc _ _ _))
  simpa only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_succ, Tm.subst_zero] using k

/-- `P(zf y, nz y) = 1`. -/
theorem p_zf_nz (t : Tm n) :
    K Γ (.eq (Tm.sel (Tm.sel t (succ zero) zero)
        (Tm.sel (Tm.sel t zero (succ zero)) zero (succ zero))
        (Tm.sel (Tm.sel t zero (succ zero)) (succ zero) zero)) (succ zero)) := by
  have k := cases (Γ := Γ)
    (Tm.sel (Tm.sel (Syn.var 0) (succ zero) zero)
      (Tm.sel (Tm.sel (Syn.var 0) zero (succ zero)) zero (succ zero))
      (Tm.sel (Tm.sel (Syn.var 0) zero (succ zero)) (succ zero) zero)) (succ zero) t
    (fun Δ => by
      simp only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_succ, Tm.subst_zero]
      exact trans (selCongr _ _ (selZero _ _)) (trans (selSucc _ _ _)
        (trans (selCongr _ _ (selZero _ _)) (selZero _ _))))
    (fun Δ => by
      simp only [Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Tm.subst_succ, Tm.subst_zero]
      exact trans (selCongr _ _ (selSucc _ _ _)) (trans (selZero _ _)
        (trans (selCongr _ _ (selSucc _ _ _)) (selSucc _ _ _))))
  simpa only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_succ, Tm.subst_zero] using k

/-- **The successor has no fixed point**: without `Q` by progress, the kernel
derives `0 = 1` from `S c = c`. -/
theorem no_succ_fixed {c : Tm n} (e : K Γ (.eq (succ c) c)) : K Γ NFm.bot := by
  -- `v = I(c, 0; u. zf u)` satisfies `v = zf v`
  have k₁ := congr (iter (Syn.var 0) zero (Tm.sel (Syn.var 0) (succ zero) zero)) e
  simp only [Tm.subst_iter, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.up_zero,
    Tm.subst_succ, Tm.subst_zero] at k₁
  have k₂ := FPrf.iterSucc (r := Rules.noInd) (Γ := Γ) rfl c zero
    (Tm.sel (Syn.var 0) (succ zero) zero)
  simp only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_succ, Tm.subst_zero] at k₂
  have hv := trans (symm k₁) k₂
  -- `zf v = nz v`
  have hgn := trans (selCongr (succ zero) zero hv) (zf_zf _)
  -- `P(zf v, nz v) = P(zf v, zf v)`
  have cP := congr (Tm.sel (Syn.shift (Tm.sel (iter c zero (Tm.sel (Syn.var 0) (succ zero) zero))
      (succ zero) zero)) (Tm.sel (Syn.var 0) zero (succ zero))
      (Tm.sel (Syn.var 0) (succ zero) zero)) (symm hgn)
  simp only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, Tm.subst_succ,
    Tm.subst_zero] at cP
  exact symm (trans (symm (p_zf_nz _)) (trans cP (p_diag _)))

/-- In the kernel without `Q` by progress, `S x = x` is contradictory. -/
theorem succ_ne_self :
    K [NFm.eq (succ (Syn.var 0 : Tm 1)) (Syn.var 0)] NFm.bot :=
  no_succ_fixed (.hyp rfl List.mem_cons_self)

end NoInd

end LeanProofs.ConciseIPRA
