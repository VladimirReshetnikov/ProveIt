import ConciseIPRA.NativeOneIntro

/-!
# Computational equality: six rules

`EPrf` is the calculus of the package `Research/computational_equality`.
Terms and formulas are those of the kernel, with ordinary substitution.  Its
rules are hypothesis, reflexivity, `QE`, `DE`, the single introduction `dI` of
`NativeOneIntro`, and one rule **Eval** that combines equality with one step of
computation: from `s = t` and `b = r` infer `r = Φ(s, t, b)`, where `Φ` is
defined in exactly three syntactic cases,

* `b` is `s`:                                  `Φ = t`;
* `b` is `I(0, a; u.h)` and `s` is `a`:        `Φ = t`;
* `b` is `I(S c, a; u.h)` and `s` is `I(c, a; u.h)`:  `Φ = h[t/u]`.

The three cases are the constructors `evalId`, `evalZero` and `evalSucc`.
There is no computation axiom and no transport rule with a template.

`eprf_iff_nprf` proves that `EPrf` derives the same sequents as the kernel.
Both computation equations are Eval applied to two reflexivities.  Transport
in a term template `h` along `s = t` is one iteration: with
`J₀ = I(0, s; u.h)` and `J₁ = I(S 0, s; u.h)`, Eval gives `J₁ = h(s)` from
`J₀ = s`, and `u = h(t)` from `J₀ = t` and `J₁ = u`.  No induction is used.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n : ℕ}

/-- Derivability with reflexivity and the rule Eval in place of the
computation equations and transport, and a single introduction rule. -/
inductive EPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : EPrf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : EPrf Γ (.eq t t)
  /-- Eval, first case: from `s = t` and `s = r` infer `r = t`. -/
  | evalId {n : ℕ} {Γ : List (NFm n)} {s t r : Tm n}
      (h₁ : EPrf Γ (.eq s t)) (h₂ : EPrf Γ (.eq s r)) : EPrf Γ (.eq r t)
  /-- Eval, second case: from `a = t` and `I(0, a; u.h) = r` infer `r = t`. -/
  | evalZero {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {a t r : Tm n}
      (h₁ : EPrf Γ (.eq a t)) (h₂ : EPrf Γ (.eq (iter zero a h) r)) : EPrf Γ (.eq r t)
  /-- Eval, third case: from `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer
  `r = h[t/u]`. -/
  | evalSucc {n : ℕ} {Γ : List (NFm n)} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n}
      (h₁ : EPrf Γ (.eq (iter c a h) t)) (h₂ : EPrf Γ (.eq (iter (succ c) a h) r)) :
      EPrf Γ (.eq r (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : EPrf Γ (.Q B)) (h₂ : EPrf Γ (B.subst (inst zero))) : EPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : EPrf Γ (.D B)) (h₂ : EPrf (.Q B :: Γ.map NFm.shift) A.shift) : EPrf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : EPrf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      EPrf Γ (.D B)

namespace EPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem eqSymm {s t : Tm n} (h : EPrf Γ (.eq s t)) : EPrf Γ (.eq t s) := .evalId (.refl s) h

theorem eqTrans {s t u : Tm n} (h₁ : EPrf Γ (.eq s t)) (h₂ : EPrf Γ (.eq t u)) :
    EPrf Γ (.eq s u) :=
  .evalId h₂ (eqSymm h₁)

/-- The zero computation, by Eval on two reflexivities. -/
theorem iterZero (a : Tm n) (h : Tm (n + 1)) : EPrf Γ (.eq (iter zero a h) a) :=
  .evalZero h (.refl a) (.refl _)

/-- The successor computation, by Eval on two reflexivities. -/
theorem iterSucc (c a : Tm n) (h : Tm (n + 1)) :
    EPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h)) :=
  .evalSucc (.refl (iter c a h)) (.refl _)

/-- Transport in one term, by one iteration of the template. -/
theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (h₁ : EPrf Γ (.eq s t))
    (h₂ : EPrf Γ (.eq (Syn.subst (inst s) h) u)) : EPrf Γ (.eq u (Syn.subst (inst t) h)) :=
  .evalSucc (eqTrans (iterZero s h) h₁)
    (eqTrans (.evalSucc (iterZero s h) (.refl (iter (succ zero) s h))) h₂)

instance : WKernel @EPrf :=
  ⟨fun h => .hyp h, fun a h => iterZero a h,
    fun a b => fun h₁ h₂ => trOne b h₁ (trOne a h₁ h₂),
    fun t h₁ h₂ => .qE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂, fun B t h => .dI B t h⟩

theorem toNPrf (h : EPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact NPrf.eqRefl t
  | @evalId _ _ s t r _ _ ih₁ ih₂ => exact .trOne (s := s) (t := t) (u := r) (Syn.var 0) ih₁ ih₂
  | evalZero h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterZero _ h) ih₁)
  | @evalSucc _ _ c a h t r _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterSucc c a h) (NPrf.eqCongr h ih₁))
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDI B t ih

end EPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem NPrf.toEPrf (h : NPrf Γ A) : EPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact EPrf.iterZero a h
  | iterSucc c a h => exact EPrf.iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact EPrf.trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact WKernel.dICase B t ih
  | qIInd s t _ ih => exact WKernel.qInd s t ih

/-- **Computational equality.**  Six rules, with one rule for equality and
computation, derive the same sequents as the kernel. -/
theorem eprf_iff_nprf : EPrf Γ A ↔ NPrf Γ A := ⟨EPrf.toNPrf, NPrf.toEPrf⟩

/-- The six-rule calculus derives the same sequents as the calculus of the
research reports. -/
theorem eprf_iff_iprf : EPrf Γ A ↔ IPrf Γ A := eprf_iff_nprf.trans iprf_iff_nprf.symm

end LeanProofs.ConciseIPRA
