import ConciseIPRA.NativeEq

/-!
# One-context transport at sources other than the literal zero

The transport rule of the kernel, from `s = t` and `h(s) = u` infer
`u = h(t)`, is the proposal of the package `Research/one_context`.  This
module shows that for this rule the restriction of the source `s` to terms
other than the literal `0` costs nothing.

`OPrf` is the kernel with that restriction.  `oprf_iff_nprf` proves that it
derives the same sequents.  The argument uses two rules only, the first
computation equation and the restricted transport, collected in the class
`OKernel`:

* a constant template reverses any equation in one step (`eqSymm`), whatever
  its sides, because the major premise can be `I(0, 0; u. 0) = 0`;
* a term `p` other than the literal `0` with `p = 0` is equal to the anchor
  `I(0, 0; u. 0)`, by transport of `I(0, p; u. 0) = p` (`toAnchor`), so two
  such terms are equal (`zeroJoin`);
* transitivity through a middle term other than the literal `0` is one step,
  and through the literal `0` it is `zeroJoin` (`eqTrans`);
* transport along `0 = t` is transport along `t = 0` followed by
  transitivity (`trOneF`).

No induction, no numerical cases and no successor computation is used.
Compare `NativeZeroSource`: for transport in an equation template with an
uncrossed conclusion, the same restriction needs an equation induction and a
singleton test.  The package `Research/reversal_core` obtains the short
argument by reversing both transport and `QE`; here `QE` is unchanged.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n : ℕ}

/-- The two rules that the elimination of the source restriction uses. -/
class OKernel (P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop) : Prop where
  iterZero : ∀ {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)),
    P Γ (.eq (iter zero a h) a)
  trOne : ∀ {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}, s ≠ zero →
    P Γ (.eq s t) → P Γ (.eq (Syn.subst (inst s) h) u) → P Γ (.eq u (Syn.subst (inst t) h))

namespace OKernel

variable {P : ∀ {n : ℕ}, List (NFm n) → NFm n → Prop} [OKernel @P] {Γ : List (NFm n)}

omit [OKernel @P] in
theorem castEq {A B : NFm n} (h : P Γ A) (e : A = B) : P Γ B := e ▸ h

theorem iterNeZero (c a : Tm n) (h : Tm (n + 1)) : iter c a h ≠ zero := fun e => by cases e

/-- From `s = t` and `s = u` infer `u = t`, for `s` other than the literal `0`. -/
theorem euclid {s t u : Tm n} (hs : s ≠ zero) (h₁ : P Γ (.eq s t)) (h₂ : P Γ (.eq s u)) :
    P Γ (.eq u t) :=
  trOne (P := @P) (s := s) (t := t) (u := u) (Syn.var 0) hs h₁ h₂

theorem eqRefl (t : Tm n) : P Γ (.eq t t) :=
  euclid (iterNeZero _ _ _) (iterZero t (Syn.var 0)) (iterZero t (Syn.var 0))

/-- Symmetry at every source: a constant template reverses an equation. -/
theorem eqSymm {s t : Tm n} (h : P Γ (.eq s t)) : P Γ (.eq t s) :=
  castEq (trOne (P := @P) (u := t) (Syn.shift s) (iterNeZero zero zero zero)
    (iterZero zero zero) (castEq h (by simp))) (by simp)

/-- A term other than the literal `0` that is provably zero is equal to the
anchor `I(0, 0; u. 0)`. -/
theorem toAnchor {p : Tm n} (hp : p ≠ zero) (h : P Γ (.eq p zero)) :
    P Γ (.eq p (iter zero zero zero)) :=
  castEq (trOne (P := @P) (u := p) (iter zero (Syn.var 0) zero) hp h
    (castEq (iterZero p zero) (by simp))) (by simp)

theorem zeroJoin {p q : Tm n} (hp : p ≠ zero) (hq : q ≠ zero) (h₁ : P Γ (.eq p zero))
    (h₂ : P Γ (.eq q zero)) : P Γ (.eq p q) :=
  euclid (iterNeZero zero zero zero) (eqSymm (toAnchor hq h₂)) (eqSymm (toAnchor hp h₁))

/-- Transitivity; only a literal-zero middle term needs the anchor. -/
theorem eqTrans {r s t : Tm n} (h₁ : P Γ (.eq r s)) (h₂ : P Γ (.eq s t)) : P Γ (.eq r t) := by
  classical
  by_cases hs : s = zero
  · subst hs
    by_cases hr : r = zero
    · subst hr; exact h₂
    · by_cases ht : t = zero
      · subst ht; exact h₁
      · exact zeroJoin hr ht h₁ (eqSymm h₂)
  · exact euclid hs h₂ (eqSymm h₁)

/-- One-context transport at every source. -/
theorem trOneF (h : Tm (n + 1)) {s t u : Tm n} (h₁ : P Γ (.eq s t))
    (h₂ : P Γ (.eq (Syn.subst (inst s) h) u)) : P Γ (.eq u (Syn.subst (inst t) h)) := by
  classical
  by_cases hs : s = zero
  · subst hs
    by_cases ht : t = zero
    · subst ht; exact eqSymm h₂
    · exact eqSymm (eqTrans (trOne (P := @P) h ht (eqSymm h₁) (eqRefl _)) h₂)
  · exact trOne h hs h₁ h₂

/-- Transport in an equation template at every source. -/
theorem trEq (a b : Tm (n + 1)) {s t : Tm n} (h₁ : P Γ (.eq s t))
    (h₂ : P Γ (.eq (Syn.subst (inst s) a) (Syn.subst (inst s) b))) :
    P Γ (.eq (Syn.subst (inst t) a) (Syn.subst (inst t) b)) :=
  trOneF b h₁ (trOneF a h₁ h₂)

end OKernel

/-- Derivability in the kernel with transport restricted to sources other than
the literal `0`. -/
inductive OPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : OPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      OPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      OPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- Tr: from `s = t` and `h(s) = u` infer `u = h(t)`, provided `s` is not
  the literal `0`. -/
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n} (hs : s ≠ zero)
      (h₁ : OPrf Γ (.eq s t)) (h₂ : OPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      OPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : OPrf Γ (.Q B)) (h₂ : OPrf Γ (B.subst (inst zero))) : OPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : OPrf Γ (.D B)) (h₂ : OPrf (.Q B :: Γ.map NFm.shift) A.shift) : OPrf Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : OPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      OPrf Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : OPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      OPrf Γ (.Q (.eq s₁ s₂))

instance : OKernel @OPrf :=
  ⟨fun a h => .iterZero a h, fun h => fun hs h₁ h₂ => .trOne h hs h₁ h₂⟩

variable {Γ : List (NFm n)} {A : NFm n}

theorem OPrf.toNPrf (h : OPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

theorem NPrf.toOPrf (h : NPrf Γ A) : OPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact OKernel.trOneF h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

/-- **The source restriction is free for one-context transport.** -/
theorem oprf_iff_nprf : OPrf Γ A ↔ NPrf Γ A := ⟨OPrf.toNPrf, NPrf.toOPrf⟩

end LeanProofs.ConciseIPRA
