import ConciseIPRA.NativeEq

/-!
# One term context suffices for equality

Written against ProveIt commit a4e5e96c456303cf231eab2aeeb3291d8889833f.
This file has not been compiled in the delivery environment.

`OPrf` has exactly the native kernel's syntax and seven non-equality rules.
Its sole equality rule has one numerical template instead of two:

    s = t, h(s) = u  |-  u = h(t).

Sources are unrestricted. In particular the rule is stable under numerical
substitution; no literal-zero dispatch convention is part of the calculus.
Two uses of this rule recover the original two-template transport exactly.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

/-- The one-context native calculus. -/
inductive OPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : OPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      OPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      OPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (major : OPrf Γ (.eq s t))
      (minor : OPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      OPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : OPrf Γ (.Q B)) (h₂ : OPrf Γ (B.subst (inst zero))) :
      OPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : OPrf Γ (.D B)) (h₂ : OPrf (.Q B :: Γ.map NFm.shift) A.shift) :
      OPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : OPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      OPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : OPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      OPrf Γ (.Q (.eq s₁ s₂))

namespace NPrf

/-- The new equality rule is old equational transport followed by symmetry. -/
theorem trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
    (major : NPrf Γ (.eq s t))
    (minor : NPrf Γ (.eq (Syn.subst (inst s) h) u)) :
    NPrf Γ (.eq u (Syn.subst (inst t) h)) := by
  have minor' : NPrf Γ
      (.eq (Syn.subst (inst s) h) (Syn.subst (inst s) (Syn.shift u))) := by
    simpa using minor
  have transported := NPrf.trEq h (Syn.shift u) major minor'
  simpa using NPrf.eqSymm transported

end NPrf

namespace OPrf

/-- Exactly two one-context steps recover two-context transport. -/
theorem trEq {n : ℕ} {Γ : List (NFm n)} (a b : Tm (n + 1)) {s t : Tm n}
    (major : OPrf Γ (.eq s t))
    (minor : OPrf Γ
      (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    OPrf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  .trOne b major (.trOne a major minor)

/-- Translate a one-context derivation to the current native kernel. -/
theorem toNative {n : ℕ} {Γ : List (NFm n)} {A : NFm n}
    (h : OPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne f _ _ ih₁ ih₂ => exact NPrf.trOne f ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

/-- Translate a current native derivation to one-context derivations. -/
theorem ofNative {n : ℕ} {Γ : List (NFm n)} {A : NFm n}
    (h : NPrf Γ A) : OPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq a b _ _ ih₁ ih₂ => exact OPrf.trEq a b ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s₁ s₂ _ ih => exact .qIInd s₁ s₂ ih

end OPrf

/-- Exact identity-language consequence equivalence in every context. -/
theorem oprf_iff_nprf {n : ℕ} {Γ : List (NFm n)} {A : NFm n} :
    OPrf Γ A ↔ NPrf Γ A := ⟨OPrf.toNative, OPrf.ofNative⟩

end LeanProofs.ConciseIPRA
