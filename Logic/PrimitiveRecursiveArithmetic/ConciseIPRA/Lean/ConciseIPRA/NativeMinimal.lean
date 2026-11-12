import ConciseIPRA.NativeOneContext
import ConciseIPRA.NativeOneIntro

/-!
# The weakenings together: a seven-rule calculus

`MPrf` combines the weakenings of the calculus of the research reports that
the other modules establish one at a time:

* transport acts on one term (`Native`, `NativeInherited`);
* its source is not the literal `0` (`NativeOneContext`);
* there is one introduction rule (`NativeOneIntro`).

Its rules are: hypothesis; the two computation equations; `trOne`, from
`s = t` and `h(s) = u` infer `u = h(t)`, for `s` not the literal `0`; `QE`;
`DE`; and the introduction `dI`, from `Γ, B(t, η) ⊢ B(t, S z)` infer
`D_{x,y} B`, with `η = z` for a literal equation at the literal witness `0`
and `η = 0` otherwise.

`mprf_iff_nprf` proves that `MPrf` derives the same sequents as the kernel, and
so (`mprf_iff_iprf`) as the calculus of the reports.  The two generic
developments are instantiated in the order in which they depend on each other:

1. `MPrf` is an `OKernel`, so transport at every source follows without any
   induction (`OKernel.trOneF`, `OKernel.trEq`);
2. with that transport `MPrf` is a `WKernel`, which gives `Q` by progress and
   `D` by cases for every matrix and witness (`WKernel.qInd`,
   `WKernel.dICase`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n : ℕ}

/-- Derivability with one-context transport at sources other than the literal
`0` and a single introduction rule. -/
inductive MPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : MPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      MPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      MPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n} (hs : s ≠ zero)
      (h₁ : MPrf Γ (.eq s t)) (h₂ : MPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      MPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : MPrf Γ (.Q B)) (h₂ : MPrf Γ (B.subst (inst zero))) : MPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : MPrf Γ (.D B)) (h₂ : MPrf (.Q B :: Γ.map NFm.shift) A.shift) : MPrf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : MPrf ((B.subst (up (inst t))).subst (repl (NFm.start B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      MPrf Γ (.D B)

namespace MPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem toNPrf (h : MPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDI B t ih

instance : OKernel @MPrf :=
  ⟨fun a h => .iterZero a h, fun h => fun hs h₁ h₂ => .trOne h hs h₁ h₂⟩

instance : WKernel @MPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun a b => fun h₁ h₂ => OKernel.trEq a b h₁ h₂,
    fun t h₁ h₂ => .qE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂, fun B t h => .dI B t h⟩

end MPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem NPrf.toMPrf (h : NPrf Γ A) : MPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact OKernel.trOneF h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact WKernel.dICase B t ih
  | qIInd s t _ ih => exact WKernel.qInd s t ih

/-- **The seven-rule calculus derives the same sequents as the kernel.** -/
theorem mprf_iff_nprf : MPrf Γ A ↔ NPrf Γ A := ⟨MPrf.toNPrf, NPrf.toMPrf⟩

/-- **The seven-rule calculus derives the same sequents as the calculus of the
research reports.** -/
theorem mprf_iff_iprf : MPrf Γ A ↔ IPrf Γ A := mprf_iff_nprf.trans iprf_iff_nprf.symm

end LeanProofs.ConciseIPRA
