import ConciseIPRA.NativeUniformClauses

/-!
# The prefix form of a `Q`-free formula

The package `Research/prefix_clauses` stores a formula of the clause calculi
as `[k, s, t]`, read `D^k (s = t)`: a chain of `k` binders `D` ending in one
equation.  This module proves the representation that the format rests on.

`NFm.Pre k A` says that `A` is `k` binders `D` followed by one equation.  A
formula has such a form exactly when it is `Q`-free (`NFm.qfree_iff_pre`); the
length `k` is the number of its binders, so it is unique (`NFm.Pre.unique`);
and it is unchanged by substitution (`NFm.Pre.subst`), so that opening a
formula acts on its two terms only.

The calculus of the package is the calculus `VPrf` of `NativeUniformClauses`
on this representation; from `Q`-free clauses `VPrf` derives only formulas of
this form (`VPrf.pre`).
-/

namespace LeanProofs.ConciseIPRA

open Syn

variable {n m : ℕ}

namespace NFm

/-- `Pre k A`: the formula `A` is `k` binders `D` followed by one equation. -/
inductive Pre : ℕ → {n : ℕ} → NFm n → Prop
  | eq {n : ℕ} (s t : Tm n) : Pre 0 (.eq s t)
  | D {n k : ℕ} {B : NFm (n + 2)} (h : Pre k B) : Pre (k + 1) (.D B)

/-- The number of binders of a formula. -/
def depth : {n : ℕ} → NFm n → ℕ
  | _, .eq _ _ => 0
  | _, .Q B => depth B + 1
  | _, .D B => depth B + 1

theorem Pre.qfree {k : ℕ} {A : NFm n} (h : Pre k A) : A.QFree := by
  induction h with
  | eq s t => trivial
  | D _ ih => exact ih

theorem Pre.depth_eq {k : ℕ} {A : NFm n} (h : Pre k A) : A.depth = k := by
  induction h with
  | eq s t => rfl
  | D _ ih => exact congrArg (· + 1) ih

/-- The prefix length is unique. -/
theorem Pre.unique {k k' : ℕ} {A : NFm n} (h : Pre k A) (h' : Pre k' A) : k = k' :=
  h.depth_eq.symm.trans h'.depth_eq

theorem pre_of_qfree (A : NFm n) (h : A.QFree) : Pre A.depth A := by
  induction A with
  | eq s t => exact .eq s t
  | Q B _ => exact h.elim
  | D B ih => exact .D (ih h)

/-- **The prefix form.**  A formula is `Q`-free exactly when it is a chain of
binders `D` ending in one equation. -/
theorem qfree_iff_pre (A : NFm n) : A.QFree ↔ ∃ k, Pre k A :=
  ⟨fun h => ⟨_, pre_of_qfree A h⟩, fun ⟨_, h⟩ => h.qfree⟩

/-- Substitution does not change the prefix. -/
theorem Pre.subst {k : ℕ} {A : NFm n} (h : Pre k A) :
    ∀ {m : ℕ} (σ : Fin n → Tm m), Pre k (A.subst σ) := by
  induction h with intro m σ
  | eq s t => exact .eq _ _
  | D _ ih => exact .D (ih _)

end NFm

/-- From `Q`-free clauses the calculus with uniform clauses derives only
formulas in prefix form. -/
theorem VPrf.pre {Γ : List (NFm n)} {A : NFm n} (hΓ : ∀ X ∈ Γ, X.QFree)
    (h : VPrf (UCl.refl :: Γ.map UCl.asm) A) : ∃ k, NFm.Pre k A := by
  refine (NFm.qfree_iff_pre A).1 ((vprf_iff_cprf.1 h).qfree fun c hc => ?_)
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hc
  exact ⟨trivial, (NFm.qfree_subst X _).2 (hΓ X hX)⟩

end LeanProofs.ConciseIPRA
