import ConciseIPRA.NativeOneIntro

/-!
# One numerical context with one introduction rule

Written against ProveIt commit a4e5e96c456303cf231eab2aeeb3291d8889833f.
This file has NOT been compiled in the delivery environment.

`O7Prf` replaces only `WPrf.trEq` by the one-context crossed rule

    s = t, h(s) = u  |-  u = h(t).

It retains the repository's single introduction rule and its exact
`NFm.start` convention: the start is the fresh variable for a literal
equation at the literal witness zero, and zero otherwise. Thus this
calculus has seven primitive constructors, just as `WPrf` does. The new
contribution reduces the equality template from two terms to one; the
single-introduction construction itself is inherited.

The equality rule is stable under numerical substitution. The entire
seven-rule calculus inherits `WPrf`'s syntactic-witness dispatch, whose
substitution theorem does not follow by a direct constructor induction.
No such induction or structural rule is used in the equivalence below.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

/-- Seven primitive rules, with one numerical equality context. -/
inductive O7Prf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : O7Prf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      O7Prf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      O7Prf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (major : O7Prf Γ (.eq s t))
      (minor : O7Prf Γ (.eq (Syn.subst (inst s) h) u)) :
      O7Prf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : O7Prf Γ (.Q B)) (h₂ : O7Prf Γ (B.subst (inst zero))) :
      O7Prf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : O7Prf Γ (.D B)) (h₂ : O7Prf (.Q B :: Γ.map NFm.shift) A.shift) :
      O7Prf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : O7Prf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      O7Prf Γ (.D B)

namespace WPrf

/-- One-context transport is available in the existing seven-rule calculus. -/
theorem trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
    (major : WPrf Γ (.eq s t))
    (minor : WPrf Γ (.eq (Syn.subst (inst s) h) u)) :
    WPrf Γ (.eq u (Syn.subst (inst t) h)) := by
  have minor' : WPrf Γ
      (.eq (Syn.subst (inst s) h) (Syn.subst (inst s) (Syn.shift u))) := by
    simpa using minor
  have transported := WPrf.trEq h (Syn.shift u) major minor'
  simpa using WPrf.eqSymm transported

end WPrf

namespace O7Prf

/-- Two one-context steps recover the existing two-context rule. -/
theorem trEq {n : ℕ} {Γ : List (NFm n)} (a b : Tm (n + 1)) {s t : Tm n}
    (major : O7Prf Γ (.eq s t))
    (minor : O7Prf Γ
      (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    O7Prf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  .trOne b major (.trOne a major minor)

theorem toWPrf {n : ℕ} {Γ : List (NFm n)} {A : NFm n}
    (h : O7Prf Γ A) : WPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne f _ _ ih₁ ih₂ => exact WPrf.trOne f ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

theorem ofWPrf {n : ℕ} {Γ : List (NFm n)} {A : NFm n}
    (h : WPrf Γ A) : O7Prf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq a b _ _ ih₁ ih₂ => exact O7Prf.trEq a b ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

end O7Prf

/-- Exact equivalence with the repository's seven-rule presentation. -/
theorem o7prf_iff_wprf {n : ℕ} {Γ : List (NFm n)} {A : NFm n} :
    O7Prf Γ A ↔ WPrf Γ A := ⟨O7Prf.toWPrf, O7Prf.ofWPrf⟩

/-- Exact equivalence with the main native kernel. -/
theorem o7prf_iff_nprf {n : ℕ} {Γ : List (NFm n)} {A : NFm n} :
    O7Prf Γ A ↔ NPrf Γ A := o7prf_iff_wprf.trans wprf_iff_nprf

end LeanProofs.ConciseIPRA
