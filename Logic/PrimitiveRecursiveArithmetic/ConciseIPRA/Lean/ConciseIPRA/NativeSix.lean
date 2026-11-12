import ConciseIPRA.NativeDiagonal

/-!
# Six rules, closed under substitution

`SPrf` combines two of the delivered ideas that the packages state separately:

* the rule **Eval** of `Research/computational_equality` and
  `Research/equality_from_iteration`, which replaces both computation
  equations and transport: from `s = t` and `b = r` infer `r = Φ(s, t, b)`,
  with `Φ = t` if `b` is `I(0, s; u.h)` and `Φ = h[t/u]` if `b` is
  `I(S c, a; u.h)` and `s` is `I(c, a; u.h)`;
* the introduction of `Research/diagonal_guard`, whose mode is read off the
  diagonal shape of the matrix.

Its rules are hypothesis, reflexivity, Eval, `QE`, `DE` and that introduction:
six rules on the terms and formulas of the kernel, with ordinary substitution,
no computation axiom, no template and no test on a witness.

* `sprf_iff_nprf`: `SPrf` derives the same sequents as the kernel;
* `SPrf.subst`: it is closed under substitution by a direct induction on
  derivations.  The six-rule calculus `EPrf` of `NativeEval` is not, because
  its introduction tests the witness for being the literal `0`.

The equivalence needs no structural rule of `SPrf`: every rule of `GPrf` is a
derived rule of `SPrf` (`SPrf.ofGPrf`), and `GPrf` is already complete.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

/-- Derivability with reflexivity, Eval and the diagonal introduction. -/
inductive SPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : SPrf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : SPrf Γ (.eq t t)
  /-- Eval at a zero iteration: from `a = t` and `I(0, a; u.h) = r` infer
  `r = t`. -/
  | evalZero {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {a t r : Tm n}
      (h₁ : SPrf Γ (.eq a t)) (h₂ : SPrf Γ (.eq (iter zero a h) r)) : SPrf Γ (.eq r t)
  /-- Eval at a successor iteration: from `I(c, a; u.h) = t` and
  `I(S c, a; u.h) = r` infer `r = h[t/u]`. -/
  | evalSucc {n : ℕ} {Γ : List (NFm n)} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n}
      (h₁ : SPrf Γ (.eq (iter c a h) t)) (h₂ : SPrf Γ (.eq (iter (succ c) a h) r)) :
      SPrf Γ (.eq r (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : SPrf Γ (.Q B)) (h₂ : SPrf Γ (B.subst (inst zero))) : SPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : SPrf Γ (.D B)) (h₂ : SPrf (.Q B :: Γ.map NFm.shift) A.shift) : SPrf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : SPrf ((B.subst (up (inst t))).subst (repl (NFm.dstart B)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      SPrf Γ (.D B)

namespace SPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem evalId {s t r : Tm n} (h₁ : SPrf Γ (.eq s t)) (h₂ : SPrf Γ (.eq s r)) :
    SPrf Γ (.eq r t) :=
  .evalZero (Syn.var 0) h₁ (.evalZero (Syn.var 0) h₂ (.refl _))

theorem eqSymm {s t : Tm n} (h : SPrf Γ (.eq s t)) : SPrf Γ (.eq t s) := evalId (.refl s) h

theorem eqTrans {s t u : Tm n} (h₁ : SPrf Γ (.eq s t)) (h₂ : SPrf Γ (.eq t u)) :
    SPrf Γ (.eq s u) :=
  evalId h₂ (eqSymm h₁)

theorem iterZero (a : Tm n) (h : Tm (n + 1)) : SPrf Γ (.eq (iter zero a h) a) :=
  .evalZero h (.refl a) (.refl _)

theorem iterSucc (c a : Tm n) (h : Tm (n + 1)) :
    SPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h)) :=
  .evalSucc (.refl (iter c a h)) (.refl _)

theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (h₁ : SPrf Γ (.eq s t))
    (h₂ : SPrf Γ (.eq (Syn.subst (inst s) h) u)) : SPrf Γ (.eq u (Syn.subst (inst t) h)) :=
  .evalSucc (eqTrans (iterZero s h) h₁)
    (eqTrans (.evalSucc (iterZero s h) (.refl (iter (succ zero) s h))) h₂)

/-- Every rule of the calculus with the diagonal introduction is a derived
rule. -/
theorem ofGPrf (h : GPrf Γ A) : SPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact iterZero a h
  | iterSucc c a h => exact iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

theorem toNPrf (h : SPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact NPrf.eqRefl t
  | evalZero h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterZero _ h) ih₁)
  | @evalSucc _ _ c a h t r _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterSucc c a h) (NPrf.eqCongr h ih₁))
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDIG B t ih

/-- Substitution of terms for the free variables of a derivation, by direct
induction: no rule tests a witness or a transport source. -/
theorem subst (h : SPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    SPrf (Γ.map fun B => B.subst σ) (A.subst σ) := by
  induction h with
  | hyp h => intro m σ; exact .hyp (List.mem_map_of_mem h)
  | refl t => intro m σ; exact .refl _
  | evalZero h _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    rw [NFm.subst_eq, Tm.subst_iter] at h₂
    exact .evalZero _ (ih₁ σ) h₂
  | evalSucc _ _ ih₁ ih₂ =>
    intro m σ
    have h₁ := ih₁ σ
    have h₂ := ih₂ σ
    rw [NFm.subst_eq, Tm.subst_iter] at h₁ h₂
    rw [NFm.subst_eq, Syn.subst_subst_inst]
    exact .evalSucc h₁ h₂
  | qE t _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ σ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m σ
    have h := ih₂ (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ σ) h
  | dI B t _ ih =>
    intro m σ
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ,
      NFm.subst_repl_up _ (NFm.dstart B) σ, NFm.subst_up_inst, ← NFm.dstart_subst] at h
    exact .dI _ _ h

end SPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Six rules, closed under substitution, derive the same sequents as the
kernel.** -/
theorem sprf_iff_nprf : SPrf Γ A ↔ NPrf Γ A :=
  ⟨SPrf.toNPrf, fun h => SPrf.ofGPrf h.toGPrf⟩

/-- `SPrf` derives the same sequents as the calculus of the research reports. -/
theorem sprf_iff_iprf : SPrf Γ A ↔ IPrf Γ A := sprf_iff_nprf.trans iprf_iff_nprf.symm

end LeanProofs.ConciseIPRA
