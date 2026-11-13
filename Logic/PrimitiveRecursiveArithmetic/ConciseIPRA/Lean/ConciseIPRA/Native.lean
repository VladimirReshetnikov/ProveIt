import ConciseIPRA.Scalar

/-!
# The native scalar core

The concise calculus itself.  Its terms are the iterator terms; its formulas
are generated from equations by two binders,

* `Q B`, binding one variable `y`, read `B(0) → ∀ y, B(y)`, and
* `D B`, binding `x` and then `y`, read `∃ x, (B(x, 0) → ∀ y, B(x, y))`.

In `D B` the variable `y` has index `0` and `x` has index `1`.

There are no connectives and no logical axioms.  The inference rules are
hypothesis, the two computation equations, transport along an equation in one
term, elimination of `Q`, elimination of `D`, introduction of `D` by cases
(any matrix), and introduction of `Q` by progress (literal equations only).  Freshness side conditions of the informal presentation are expressed
by de Bruijn scoping: a fresh variable is the new index `0` over a weakened
context.

Two rules are weaker than in the research reports, with the same derivable
sequents (`NativeInherited`):

* transport acts on one term: from `s = t` and `h(s) = u` it infers
  `u = h(t)`, the rule of the package `Research/one_context`.  Transport in an
  equation template, `NPrf.trEq`, is two steps, and transport in an arbitrary
  formula template is the derived rule `NPrf.tr` (`NativeEq`);
* progress introduces `Q_y E(y)` directly; the reports' witnessed form, which
  introduces `D_{x,y} E(x, y)`, is the derived rule `NPrf.dIProg`.

`NFm.toFm` is the ordinary reading into first-order formulas over the same
terms.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter one)

/-- Native formulas over `n` free variables. -/
inductive NFm : ℕ → Type
  | eq {n : ℕ} (s t : Tm n) : NFm n
  | Q {n : ℕ} (B : NFm (n + 1)) : NFm n
  | D {n : ℕ} (B : NFm (n + 2)) : NFm n

namespace NFm

variable {n m k : ℕ}

/-- Simultaneous substitution in a native formula. -/
def subst : {n m : ℕ} → NFm n → (Fin n → Tm m) → NFm m
  | _, _, eq s t, σ => eq (Syn.subst σ s) (Syn.subst σ t)
  | _, _, Q B, σ => Q (B.subst (up σ))
  | _, _, D B, σ => D (B.subst (up (up σ)))

/-- Weakening by one new variable with index `0`. -/
def shift (A : NFm n) : NFm (n + 1) := A.subst (fun i => var i.succ)

@[simp] theorem subst_eq (s t : Tm n) (σ : Fin n → Tm m) :
    (eq s t).subst σ = eq (Syn.subst σ s) (Syn.subst σ t) := rfl
@[simp] theorem subst_Q (B : NFm (n + 1)) (σ : Fin n → Tm m) :
    (Q B).subst σ = Q (B.subst (up σ)) := rfl
@[simp] theorem subst_D (B : NFm (n + 2)) (σ : Fin n → Tm m) :
    (D B).subst σ = D (B.subst (up (up σ))) := rfl

/-- The ordinary reading of a native formula. -/
def toFm : {n : ℕ} → NFm n → Fm Tm n
  | _, eq s t => s ≐ t
  | _, Q B => (toFm B).subst (inst zero) ⟶ Fm.all (toFm B)
  | _, D B => Fm.ex ((toFm B).subst (inst zero) ⟶ Fm.all (toFm B))

@[simp] theorem toFm_eq (s t : Tm n) : (eq s t).toFm = (s ≐ t) := rfl
@[simp] theorem toFm_Q (B : NFm (n + 1)) :
    (Q B).toFm = (B.toFm.subst (inst zero) ⟶ Fm.all B.toFm) := rfl
@[simp] theorem toFm_D (B : NFm (n + 2)) :
    (D B).toFm = Fm.ex (B.toFm.subst (inst zero) ⟶ Fm.all B.toFm) := rfl

/-- The ordinary reading commutes with substitution. -/
theorem toFm_subst (A : NFm n) :
    ∀ {m : ℕ} (σ : Fin n → Tm m), (A.subst σ).toFm = A.toFm.subst σ := by
  induction A with intro m σ
  | eq s t => rfl
  | Q B ih =>
    simp only [subst_Q, toFm_Q, ih, Fm.subst_imp, Fm.subst_all, Fm.subst_inst, Tm.subst_zero]
  | D B ih =>
    simp only [subst_D, toFm_D, ih, Fm.subst_ex, Fm.subst_imp, Fm.subst_all, Fm.subst_inst,
      Tm.subst_zero]

theorem toFm_shift (A : NFm n) : A.shift.toFm = A.toFm.shift := toFm_subst A _

theorem map_toFm_shift (Γ : List (NFm n)) :
    (Γ.map shift).map toFm = (Γ.map toFm).map Fm.shift := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => simp only [List.map_cons, ih, toFm_shift]

end NFm

/-- Derivability in the native scalar core. -/
inductive NPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  /-- Hyp. -/
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : NPrf Γ A
  /-- `I(0, a; u.h) = a`. -/
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      NPrf Γ (.eq (iter zero a h) a)
  /-- `I(S c, a; u.h) = h[I(c, a; u.h)/u]`. -/
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      NPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  /-- Tr: transport along an equation in one term template: from `s = t` and
  `h(s) = u` infer `u = h(t)`. -/
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : NPrf Γ (.eq s t)) (h₂ : NPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      NPrf Γ (.eq u (Syn.subst (inst t) h))
  /-- QE: from `Q_y B(y)` and `B(0)` infer `B(t)`. -/
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : NPrf Γ (.Q B)) (h₂ : NPrf Γ (B.subst (inst zero))) : NPrf Γ (B.subst (inst t))
  /-- DE: from `D_{x,y} B` and a derivation of `A` from `Q_y B(b, y)` with `b`
  fresh, infer `A`. -/
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : NPrf Γ (.D B)) (h₂ : NPrf (.Q B :: Γ.map NFm.shift) A.shift) : NPrf Γ A
  /-- DI by cases: from `B(t, 0) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`. -/
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : NPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      NPrf Γ (.D B)
  /-- QI by progress: from `E(z) ⊢ E(S z)` with `z` fresh infer
  `Q_y E(y)`, for a literal equation `E` only. -/
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : NPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      NPrf Γ (.Q (.eq s₁ s₂))

/-- Soundness of the native scalar core for its ordinary reading in `T_eq`. -/
theorem NPrf.sound {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : NPrf Γ A) :
    Γ.map NFm.toFm ⊢[TeqAx] A.toFm := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => exact Teq.iterZero a h
  | iterSucc c a h => exact Teq.iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact Prf.eqTrans (Prf.eqSymm ih₂) (Prf.eqCongr1 h ih₁)
  | qE t _ _ ih₁ ih₂ =>
    rw [NFm.toFm_subst] at ih₂ ⊢
    exact .allE t (.impE ih₁ ih₂)
  | dE _ _ ih₁ ih₂ =>
    rw [List.map_cons, NFm.map_toFm_shift, NFm.toFm_shift] at ih₂
    exact .exE ih₁ ih₂
  | dICase B t _ ih =>
    simp only [List.map_cons, NFm.map_toFm_shift, NFm.toFm_shift, NFm.toFm_subst] at ih
    rw [NFm.toFm_D]
    refine .exI t ?_
    rw [Fm.subst_imp, Fm.subst_all, Fm.subst_inst, Tm.subst_zero]
    exact .impI (Teq.caseAll _ Prf.hyp0 ih)
  | qIInd s₁ s₂ _ ih =>
    simp only [List.map_cons, NFm.map_toFm_shift, NFm.toFm_subst, NFm.toFm_eq] at ih
    rw [NFm.toFm_Q, NFm.toFm_eq]
    exact .impI (Teq.eqInd s₁ s₂ Prf.hyp0
      (ih.weaken (List.cons_subset_cons _ (List.subset_cons_self _ _))))

end LeanProofs.ConciseIPRA
