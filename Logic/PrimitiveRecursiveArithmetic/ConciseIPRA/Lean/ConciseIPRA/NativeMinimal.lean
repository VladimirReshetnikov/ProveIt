import ConciseIPRA.NativeZeroSource
import ConciseIPRA.NativeOneIntro

/-!
# The three weakenings together: a seven-rule calculus

`MPrf` combines the three weakenings of the calculus of the research reports
that the other modules establish one at a time:

* transport acts inside an equation only (`Native`, `NativeInherited`);
* its source is not the literal `0` (`NativeZeroSource`);
* there is one introduction rule (`NativeOneIntro`).

Its rules are: hypothesis; the two computation equations; `trEq`, from `s = t`
and `a(s) = b(s)` infer `a(t) = b(t)`, for `s` not the literal `0`; `QE`; `DE`;
and the introduction `dI`, from `Γ, B(t, η) ⊢ B(t, S z)` infer `D_{x,y} B`,
with `η = z` for a literal equation at the literal witness `0` and `η = 0`
otherwise.

`mprf_iff_nprf` proves that `MPrf` derives the same sequents as the kernel, and
so (`mprf_iff_iprf`) as the calculus of the reports.  The two generic
developments are instantiated in the order in which they depend on each other:

1. numerical cases and equation induction in `MPrf` need no transport: cases
   are the introduction at a dummy witness coordinate and the witness
   `I(0, 0; u. 0)`, induction is the introduction at the witness `0`;
2. so `MPrf` is a `ZKernel`, and transport at every source follows
   (`ZKernel.trF`);
3. with that transport `MPrf` is a `WKernel`, which gives `D` by cases for
   every matrix and witness (`WKernel.dICase`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n : ℕ}

/-- Derivability with equational transport at sources other than the literal
`0` and a single introduction rule. -/
inductive MPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : MPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      MPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      MPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trEq {n : ℕ} {Γ : List (NFm n)} (a b : Tm (n + 1)) {s t : Tm n} (hs : s ≠ zero)
      (h₁ : MPrf Γ (.eq s t))
      (h₂ : MPrf Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
      MPrf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b))
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
  | trEq a b _ _ _ ih₁ ih₂ => exact .trEq a b ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDI B t ih

/-- Numerical cases, by the introduction at a dummy witness coordinate and the
witness `I(0, 0; u. 0)`. -/
theorem cases (B : NFm (n + 1)) (t : Tm n) (h0 : MPrf Γ (B.subst (inst zero)))
    (hS : MPrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : MPrf Γ (B.subst (inst t)) := by
  have hD : MPrf Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine .dI _ (iter zero zero zero) ?_
    rw [NFm.start_iter, NFm.subst_dummy_inst, ← NFm.shift_subst_inst_zero]
    exact hS
  exact .qE t (.dE hD (.hyp List.mem_cons_self)) h0

/-- Equation induction, by the introduction at a dummy witness coordinate and
the witness `0`. -/
theorem eqInd (s t : Tm (n + 1)) (u : Tm n) (h0 : MPrf Γ ((NFm.eq s t).subst (inst zero)))
    (hS : MPrf (NFm.eq s t :: Γ.map NFm.shift)
      ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    MPrf Γ ((NFm.eq s t).subst (inst u)) := by
  have hD : MPrf Γ (.D ((NFm.eq s t).subst (up (fun i => Syn.var i.succ)))) := by
    refine .dI _ zero ?_
    rw [show (NFm.eq s t).subst (up (fun i => Syn.var i.succ))
        = .eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
          (Syn.subst (up (fun i => Syn.var i.succ)) t) from rfl,
      NFm.start_eq_zero, NFm.subst_repl_var,
      show (NFm.eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
        (Syn.subst (up (fun i => Syn.var i.succ)) t)).subst (up (inst zero)) = .eq s t from
      NFm.subst_dummy_inst (.eq s t) zero]
    exact hS
  exact .qE u (.dE hD (.hyp List.mem_cons_self)) h0

instance : ZKernel @MPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun c a h => .iterSucc c a h,
    fun a b => fun hs h₁ h₂ => .trEq a b hs h₁ h₂, cases, eqInd⟩

instance : WKernel @MPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun a b => fun h₁ h₂ => ZKernel.trF a b h₁ h₂,
    fun t h₁ h₂ => .qE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂, fun B t h => .dI B t h⟩

end MPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem NPrf.toMPrf (h : NPrf Γ A) : MPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq a b _ _ ih₁ ih₂ => exact ZKernel.trF a b ih₁ ih₂
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
