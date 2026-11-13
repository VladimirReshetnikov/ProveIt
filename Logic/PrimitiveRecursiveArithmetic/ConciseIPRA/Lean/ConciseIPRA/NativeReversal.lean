import ConciseIPRA.NativeBiInterpretation

/-!
# Crossed elimination with a nonliteral-zero source

This is the module proposed by the package `Research/reversal_core`
(`formalization/Reversal.lean`), compiled here; `NFm.rho` is renamed `NFm.rev`.

`RPrf` replaces equational transport by crossed transport in an arbitrary
native template, restricted to sources other than literal `0`. It also
reverses the result of closure elimination. Reversal exchanges the endpoints
of a root equation and does not descend under `Q` or `D`.

The equality normalization uses only `iterZero` and `x`: the retraction
`J a = I(0, a; u. 0)` provides a syntactically nonzero representative of
every term. Constant templates make unrestricted reversal immediate.
No derivation substitution, arithmetic induction, numerical cases, or
successor computation is used in the new equality lemmas.

Compare `NativeZeroSource`: with the uncrossed transport rule the same source
restriction needs an induction and a singleton test (`ZKernel.zeroSymm`).
With the crossed rule it needs neither.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter one)
open scoped Fm

variable {n m : ℕ}

namespace NFm

/-- Reverse a root equation; leave a compound formula unchanged. -/
def rev : {n : ℕ} → NFm n → NFm n
  | _, .eq s t => .eq t s
  | _, .Q B => .Q B
  | _, .D B => .D B

@[simp] theorem rev_eq (s t : Tm n) : (NFm.eq s t).rev = .eq t s := rfl
@[simp] theorem rev_Q (B : NFm (n + 1)) : (NFm.Q B).rev = .Q B := rfl
@[simp] theorem rev_D (B : NFm (n + 2)) : (NFm.D B).rev = .D B := rfl

@[simp] theorem rev_rev (A : NFm n) : A.rev.rev = A := by
  cases A <;> rfl

theorem rev_subst (A : NFm n) (σ : Fin n → Tm m) :
    (A.subst σ).rev = A.rev.subst σ := by
  cases A <;> rfl

end NFm

/-- The crossed calculus, with exactly eight primitive constructors. -/
inductive RPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : RPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      RPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      RPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | x {n : ℕ} {Γ : List (NFm n)} (F : NFm (n + 1)) {s t : Tm n}
      (hs : s ≠ zero) (h₁ : RPrf Γ (.eq s t))
      (h₂ : RPrf Γ (F.subst (inst s))) :
      RPrf Γ (F.subst (inst t)).rev
  | qX {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : RPrf Γ (.Q B)) (h₂ : RPrf Γ (B.subst (inst zero))) :
      RPrf Γ (B.subst (inst t)).rev
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : RPrf Γ (.D B)) (h₂ : RPrf (.Q B :: Γ.map NFm.shift) A.shift) :
      RPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : RPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      RPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : RPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      RPrf Γ (.Q (.eq s₁ s₂))

namespace NPrf

/-- Root reversal is already admissible in the old native kernel. -/
theorem rev {Γ : List (NFm n)} {A : NFm n} (h : NPrf Γ A) : NPrf Γ A.rev := by
  cases A with
  | eq s t => exact eqSymm h
  | Q B => exact h
  | D B => exact h

end NPrf

namespace RPrf

variable {Γ : List (NFm n)} {A : NFm n}

/-- The easy interpretation: crossed elimination is old transport plus reversal. -/
theorem toNPrf (h : RPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | x F _ _ _ ih₁ ih₂ => exact NPrf.rev (NPrf.tr F ih₁ ih₂)
  | qX t _ _ ih₁ ih₂ => exact NPrf.rev (.qE t ih₁ ih₂)
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

private theorem iterNeZero (c a : Tm n) (h : Tm (n + 1)) :
    iter c a h ≠ zero := by
  intro e
  cases e

/-- A nonliteral-zero anchor which computes to zero. -/
def anchor : Tm n := iter zero zero zero

private theorem anchorNeZero : (anchor : Tm n) ≠ zero :=
  iterNeZero _ _ _

/-- A named-instance form of the primitive crossed rule. -/
theorem x' (F : NFm (n + 1)) {s t : Tm n} {A B : NFm n}
    (hs : s ≠ zero) (e : RPrf Γ (.eq s t))
    (hA : F.subst (inst s) = A) (hB : F.subst (inst t) = B)
    (h : RPrf Γ A) : RPrf Γ B.rev := by
  subst hA hB
  exact .x F hs e h

/-- A constant template reverses any formula, including a zero-source equation. -/
theorem reverse (h : RPrf Γ A) : RPrf Γ A.rev := by
  have e : RPrf Γ (.eq (anchor : Tm n) zero) := .iterZero zero zero
  exact x' A.shift anchorNeZero e (by simp) (by simp) h

/-- Ordinary transport at a nonliteral-zero source. -/
theorem trRestricted (F : NFm (n + 1)) {s t : Tm n}
    (hs : s ≠ zero) (e : RPrf Γ (.eq s t))
    (h : RPrf Γ (F.subst (inst s))) : RPrf Γ (F.subst (inst t)) := by
  simpa using reverse (.x F hs e h)

theorem trRestricted' (F : NFm (n + 1)) {s t : Tm n} {A B : NFm n}
    (hs : s ≠ zero) (e : RPrf Γ (.eq s t))
    (hA : F.subst (inst s) = A) (hB : F.subst (inst t) = B)
    (h : RPrf Γ A) : RPrf Γ B := by
  subst hA hB
  exact trRestricted F hs e h

/-- Reflexivity uses two copies of a zero-computation axiom. -/
theorem eqRefl (a : Tm n) : RPrf Γ (.eq a a) := by
  have e : RPrf Γ (.eq (iter zero a zero) a) := .iterZero a zero
  exact x' (B := .eq a a) (.eq (Syn.var 0) (Syn.shift a))
    (iterNeZero _ _ _) e (by simp) (by simp) e

theorem eqSymm {s t : Tm n} (h : RPrf Γ (.eq s t)) : RPrf Γ (.eq t s) :=
  reverse h

/-- Every syntactically nonzero term provably zero can be joined to the anchor. -/
theorem toAnchor {p : Tm n} (hp : p ≠ zero) (h : RPrf Γ (.eq p zero)) :
    RPrf Γ (.eq p anchor) := by
  have e : RPrf Γ (.eq (iter zero p zero) p) := .iterZero p zero
  exact x' (B := .eq (iter zero zero zero) p) (.eq (iter zero (Syn.var 0) zero) (Syn.shift p))
    hp h (by simp) (by simp) e

/-- Join two nonliteral-zero terms provably equal to zero. -/
theorem zeroJoin {p q : Tm n} (hp : p ≠ zero) (hq : q ≠ zero)
    (h₁ : RPrf Γ (.eq p zero)) (h₂ : RPrf Γ (.eq q zero)) : RPrf Γ (.eq p q) := by
  have cp : RPrf Γ (.eq anchor p) := eqSymm (toAnchor hp h₁)
  have cq : RPrf Γ (.eq anchor q) := eqSymm (toAnchor hq h₂)
  exact x' (B := .eq q p) (.eq (Syn.var 0) (Syn.shift p)) anchorNeZero cq
    (by simp) (by simp) cp

/-- Transitivity; only the syntactic zero middle requires the anchor construction. -/
theorem eqTrans {r s t : Tm n} (h₁ : RPrf Γ (.eq r s)) (h₂ : RPrf Γ (.eq s t)) :
    RPrf Γ (.eq r t) := by
  classical
  by_cases hs : s = zero
  · subst hs
    by_cases hr : r = zero
    · subst hr
      exact h₂
    · by_cases ht : t = zero
      · subst ht
        exact h₁
      · exact zeroJoin hr ht h₁ (eqSymm h₂)
  · exact trRestricted' (.eq (Syn.shift r) (Syn.var 0)) hs h₂
      (by simp) (by simp) h₁

/-- Term congruence, including a literal-zero source. -/
theorem eqCongr (f : Tm (n + 1)) {s t : Tm n} (e : RPrf Γ (.eq s t)) :
    RPrf Γ (.eq (Syn.subst (inst s) f) (Syn.subst (inst t) f)) := by
  classical
  by_cases hs : s = zero
  · subst hs
    by_cases ht : t = zero
    · subst ht
      exact eqRefl _
    · exact trRestricted' (.eq f (Syn.shift (Syn.subst (inst t) f))) ht (eqSymm e)
        (by simp) (by simp) (eqRefl (Syn.subst (inst t) f))
  · exact trRestricted' (.eq (Syn.shift (Syn.subst (inst s) f)) f) hs e
      (by simp) (by simp) (eqRefl (Syn.subst (inst s) f))

/-- Recover exactly the equational transport constructor of `NPrf`. -/
theorem trEq (a b : Tm (n + 1)) {s t : Tm n} (e : RPrf Γ (.eq s t))
    (h : RPrf Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    RPrf Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  eqTrans (eqTrans (eqSymm (eqCongr a e)) h) (eqCongr b e)

/-- Ordinary closure elimination is crossed elimination followed by reversal. -/
theorem qE {B : NFm (n + 1)} (t : Tm n)
    (h₁ : RPrf Γ (.Q B)) (h₂ : RPrf Γ (B.subst (inst zero))) :
    RPrf Γ (B.subst (inst t)) := by
  simpa using reverse (.qX t h₁ h₂)

end RPrf

theorem NPrf.toRPrf {Γ : List (NFm n)} {A : NFm n} (h : NPrf Γ A) : RPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | @trOne _ _ h s t u _ _ ih₁ ih₂ =>
    have e := RPrf.eqSymm (RPrf.trEq h (Syn.shift u) ih₁ (by simpa using ih₂))
    simpa using e
  | qE t _ _ ih₁ ih₂ => exact RPrf.qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

/-- Identity-language equivalence over arbitrary retained contexts. -/
theorem rprf_iff_nprf {Γ : List (NFm n)} {A : NFm n} : RPrf Γ A ↔ NPrf Γ A :=
  ⟨RPrf.toNPrf, NPrf.toRPrf⟩

/-- The inherited native interpretation remains faithful. -/
theorem reversal_iff_pra {Γ : List (NFm n)} {A : NFm n} :
    RPrf Γ A ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  rprf_iff_nprf.trans native_iff_pra

/-- The reverse inherited interpretation remains faithful. -/
theorem pra_iff_reversal {Γ : List (Fm PTm n)} {φ : Fm PTm n} :
    (Γ ⊢[PRAAx] φ) ↔ RPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.trans rprf_iff_nprf.symm

/-- The native-side round trip is unchanged. -/
theorem reversal_roundTrip (A : NFm n) :
    RPrf [NFm.ofPRA A.toPRA] A ∧ RPrf [A] (NFm.ofPRA A.toPRA) :=
  ⟨(native_roundTrip A).1.toRPrf, (native_roundTrip A).2.toRPrf⟩

/-- The iPRA-side round trip has exactly its existing statement. -/
theorem pra_reversal_roundTrip (φ : Fm PTm n) (Γ : List (Fm PTm n)) :
    Γ ⊢[PRAAx] Fm.iff φ (NFm.ofPRA φ).toPRA :=
  pra_native_roundTrip φ Γ

/-- Effective equivalence at the designated contradictions. -/
theorem reversal_inconsistent_iff :
    RPrf ([] : List (NFm 0)) NFm.bot ↔ ([] ⊢[PRAAx] (Fm.bot : Fm PTm 0)) :=
  rprf_iff_nprf.trans native_inconsistent_iff

end LeanProofs.ConciseIPRA
