import ConciseIPRA.NativeMinimal
import ConciseIPRA.NativeBiInterpretation

/-!
# One-sided crossed transport

Proposed module against ProveIt commit
8eb71c1e570e07ef45ead686628e77f18ef34798.

This file has not been compiled in the delivery environment, which has no
Lean executable. It is a proposed formalization, not a verified Lean result.

`CPrf` has the same seven rule positions as `MPrf`, but its equality rule
has one numerical template instead of two:

    s = t, f(s) = r  ==>  r = f(t),   s != literal zero.

Closure elimination is unchanged. No formula-reversal operation is defined.
Two uses of this rule recover restricted two-sided equational transport.
The equality lemmas below recover unrestricted transport using only
`iterZero` and `x`; neither arithmetic induction nor logical inference is
used by those lemmas. The inherited single-introduction theorem then applies.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)
open scoped Fm

variable {n : ℕ}

/-- Seven-rule calculus with one numerical template in its equality rule. -/
inductive CPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : CPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      CPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      CPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | x {n : ℕ} {Γ : List (NFm n)} (f : Tm (n + 1)) {s t r : Tm n}
      (hs : s ≠ zero) (h₁ : CPrf Γ (.eq s t))
      (h₂ : CPrf Γ (.eq (Syn.subst (inst s) f) r)) :
      CPrf Γ (.eq r (Syn.subst (inst t) f))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : CPrf Γ (.Q B)) (h₂ : CPrf Γ (B.subst (inst zero))) :
      CPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : CPrf Γ (.D B)) (h₂ : CPrf (.Q B :: Γ.map NFm.shift) A.shift) :
      CPrf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : CPrf ((B.subst (up (inst t))).subst (repl (NFm.start B t))
        :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      CPrf Γ (.D B)

namespace NPrf

/-- The new equality rule is old equational transport followed by symmetry. -/
theorem oneSided (f : Tm (n + 1)) {Γ : List (NFm n)} {s t r : Tm n}
    (e : NPrf Γ (.eq s t))
    (h : NPrf Γ (.eq (Syn.subst (inst s) f) r)) :
    NPrf Γ (.eq r (Syn.subst (inst t) f)) := by
  apply eqSymm
  simpa using (trEq f (Syn.shift r) e (by simpa using h))

end NPrf

namespace CPrf

variable {Γ : List (NFm n)} {A : NFm n}

theorem toNPrf (h : CPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | x f _ _ _ ih₁ ih₂ => exact .oneSided f ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDI B t ih

/-- The decisive two-step simulation. The source restriction is preserved. -/
theorem trEqRestricted (a b : Tm (n + 1)) {s t : Tm n} (hs : s ≠ zero)
    (e : CPrf Γ (.eq s t))
    (h : CPrf Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    CPrf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  .x b hs e (.x a hs e h)

private theorem iterNeZero (c a : Tm n) (h : Tm (n + 1)) :
    iter c a h ≠ zero := by
  intro e
  cases e

/-- A syntactically nonzero term that computes to zero. -/
def anchor : Tm n := iter zero zero zero

private theorem anchorNeZero : (anchor : Tm n) ≠ zero := iterNeZero _ _ _

/-- Primitive `x` with names for the two numerical template instances. -/
theorem x' (f : Tm (n + 1)) {s t r a b : Tm n} (hs : s ≠ zero)
    (e : CPrf Γ (.eq s t))
    (ha : Syn.subst (inst s) f = a) (hb : Syn.subst (inst t) f = b)
    (h : CPrf Γ (.eq a r)) : CPrf Γ (.eq r b) := by
  subst a b
  exact .x f hs e h

/-- Reflexivity requires only a zero computation and one crossed inference. -/
theorem eqRefl (a : Tm n) : CPrf Γ (.eq a a) := by
  have e : CPrf Γ (.eq (iter zero a zero) a) := .iterZero a zero
  exact x' (Syn.var 0) (iterNeZero _ _ _) e (by simp) (by simp) e

/-- Constant templates reverse any equation, including a zero-source one. -/
theorem eqSymm {s t : Tm n} (h : CPrf Γ (.eq s t)) : CPrf Γ (.eq t s) :=
  x' (Syn.shift s) anchorNeZero (.iterZero zero zero) (by simp) (by simp) h

/-- A nonliteral-zero term equal to zero is connected to the anchor. -/
theorem toAnchor {p : Tm n} (hp : p ≠ zero) (h : CPrf Γ (.eq p zero)) :
    CPrf Γ (.eq p anchor) :=
  x' (iter zero (Syn.var 0) zero) hp h (by simp) (by simp) (.iterZero p zero)

/-- Joining two nonliteral-zero terms through zero uses no induction. -/
theorem zeroJoin {p q : Tm n} (hp : p ≠ zero) (hq : q ≠ zero)
    (h₁ : CPrf Γ (.eq p zero)) (h₂ : CPrf Γ (.eq q zero)) : CPrf Γ (.eq p q) := by
  have cp : CPrf Γ (.eq anchor p) := eqSymm (toAnchor hp h₁)
  have cq : CPrf Γ (.eq anchor q) := eqSymm (toAnchor hq h₂)
  exact x' (Syn.var 0) anchorNeZero cq (by simp) (by simp) cp

/-- Transitivity, with the syntactic-zero case handled by the anchor. -/
theorem eqTrans {r s t : Tm n} (h₁ : CPrf Γ (.eq r s)) (h₂ : CPrf Γ (.eq s t)) :
    CPrf Γ (.eq r t) := by
  classical
  by_cases hs : s = zero
  · subst s
    by_cases hr : r = zero
    · subst r
      exact h₂
    · by_cases ht : t = zero
      · subst t
        exact h₁
      · exact zeroJoin hr ht h₁ (eqSymm h₂)
  · exact x' (Syn.var 0) hs h₂ (by simp) (by simp) (eqSymm h₁)

/-- Numerical congruence at every source. -/
theorem eqCongr (f : Tm (n + 1)) {s t : Tm n} (e : CPrf Γ (.eq s t)) :
    CPrf Γ (.eq (Syn.subst (inst s) f) (Syn.subst (inst t) f)) := by
  classical
  by_cases hs : s = zero
  · subst s
    by_cases ht : t = zero
    · subst t
      exact eqRefl _
    · exact eqSymm (.x f ht (eqSymm e) (eqRefl _))
  · exact .x f hs e (eqRefl _)

/-- Full equational transport. This proof uses only `iterZero` and `x`. -/
theorem trEq (a b : Tm (n + 1)) {s t : Tm n} (e : CPrf Γ (.eq s t))
    (h : CPrf Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    CPrf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  eqTrans (eqTrans (eqSymm (eqCongr a e)) h) (eqCongr b e)

/-- The already-proved single-introduction development now applies directly. -/
instance : WKernel @CPrf :=
  ⟨fun h => .hyp h, fun a h => .iterZero a h, fun a b h₁ h₂ => trEq a b h₁ h₂,
    fun t h₁ h₂ => .qE t h₁ h₂, fun h₁ h₂ => .dE h₁ h₂, fun B t h => .dI B t h⟩

end CPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- A second, direct comparison with the existing seven-rule calculus. -/
theorem MPrf.toCPrf (h : MPrf Γ A) : CPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq a b hs _ _ ih₁ ih₂ => exact CPrf.trEqRestricted a b hs ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

theorem NPrf.toCPrf (h : NPrf Γ A) : CPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trEq a b _ _ ih₁ ih₂ => exact CPrf.trEq a b ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact WKernel.dICase B t ih
  | qIInd s t _ ih => exact WKernel.qInd s t ih

theorem cprf_iff_nprf : CPrf Γ A ↔ NPrf Γ A := ⟨CPrf.toNPrf, NPrf.toCPrf⟩

theorem cprf_iff_mprf : CPrf Γ A ↔ MPrf Γ A :=
  ⟨fun h => h.toNPrf.toMPrf, MPrf.toCPrf⟩

theorem oneSided_iff_pra : CPrf Γ A ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  cprf_iff_nprf.trans native_iff_pra

theorem pra_iff_oneSided {Γ : List (Fm PTm n)} {φ : Fm PTm n} :
    (Γ ⊢[PRAAx] φ) ↔ CPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.trans cprf_iff_nprf.symm

theorem oneSided_roundTrip (A : NFm n) :
    CPrf [NFm.ofPRA A.toPRA] A ∧ CPrf [A] (NFm.ofPRA A.toPRA) :=
  ⟨(native_roundTrip A).1.toCPrf, (native_roundTrip A).2.toCPrf⟩

theorem pra_oneSided_roundTrip (φ : Fm PTm n) (Γ : List (Fm PTm n)) :
    Γ ⊢[PRAAx] Fm.iff φ (NFm.ofPRA φ).toPRA :=
  pra_native_roundTrip φ Γ

theorem oneSided_inconsistent_iff :
    CPrf ([] : List (NFm 0)) NFm.bot ↔ ([] ⊢[PRAAx] (Fm.bot : Fm PTm 0)) :=
  cprf_iff_nprf.trans native_inconsistent_iff

end LeanProofs.ConciseIPRA
