import IPRADerivations.Foundations.BoundedFormulas

/-!
# Guarded finite covers and composed bounded searches

Packet: `ipra_bounded_reflection_2026-11-16`, Theorems `thm:cover` and `thm:composition`, as schemas
over bounded formulas `BF` (`Foundations/BoundedFormulas`) with packed parameters.

* `cover_at`, `cover` (`thm:cover`): if iPRA proves `∃ i < N(x) C(⟨i, x⟩)` and
  `i < N(x) → C(⟨i, x⟩) → P(x)` for an arbitrary formula `P`, then it proves `P(x)` (and `∀ x P(x)`).
  The proof instantiates the second premise at the canonical witness `w(x) = bfWit N C x`;
  no decision procedure for `P` and no induction on a quantified invariant is used.
* `composition` (`thm:composition`): from `∃ y < B(x) R(⟨y, x⟩)` and
  `y < B(x) → R(⟨y, x⟩) → ∃ z < D(⟨y, x⟩) S(⟨z, ⟨y, x⟩⟩)`, the primitive-recursive witnesses
  `w(x) = bfWit B R x` and `v(x) = bfWit D S ⟨w(x), x⟩` satisfy `R(⟨w, x⟩) ∧ S(⟨v, ⟨w, x⟩⟩)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.BoundedCover

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedFormulas
open Syn
open scoped Fm

/-- Instantiating a two-variable open premise at `![i, x]`. -/
theorem fmAt_inst2 (A : BF) {m : ℕ} (i x : PTm m) :
    (fmAt A 2 (pairT (var 0) (var 1))).subst ![i, x] = fmAt A m (pairT i x) := by
  rw [fmAt_subst]; simp [subst_pairT]

theorem at1_inst2 (N : PTm 1) {m : ℕ} (i x : PTm m) :
    Syn.subst ![i, x] (at1 N (var 1 : PTm 2)) = at1 N x := by
  rw [at1_subst]; simp

theorem at1_inst1 (N : PTm 1) {m : ℕ} (x : PTm m) : Syn.subst ![x] (at1 N (var 0 : PTm 1)) = at1 N x := by
  rw [at1_subst]; simp

variable (C : BF) (N : PTm 1) (P : Fm PTm 1)

/-- `thm:cover` at a state `x`, with the canonical witness. -/
theorem cover_at {m : ℕ} {Δ : List (Fm PTm m)}
    (h₁ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fmAt (.ex N C) 1 (var 0))
    (h₂ : ([] : List (Fm PTm 2)) ⊢[PRAAx]
      lt (var 0) (at1 N (var 1)) ⟶ fmAt C 2 (pairT (var 0) (var 1)) ⟶ P.subst ![var 1])
    (x : PTm m) : Δ ⊢[PRAAx] P.subst ![x] := by
  have e₁ := inst (Γ := Δ) h₁ ![x]
  rw [fmAt_subst] at e₁
  simp only [Syn.subst_var, Matrix.cons_val_zero] at e₁
  have c := bf_choice N C x e₁
  have e₂ := inst (Γ := Δ) h₂ ![bfWit N C x, x]
  simp only [Fm.subst_imp, subst_lt, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, at1_inst2, fmAt_inst2, Fm.subst_subst] at e₂
  have eP : P.subst (fun j => Syn.subst ![bfWit N C x, x] (![var 1] j : PTm 2)) = P.subst ![x] := by
    congr 1; funext j; fin_cases j; rfl
  rw [eP] at e₂
  exact Prf.impE (Prf.impE e₂ (Prf.andE₁ c)) (Prf.andE₂ c)

/-- `thm:cover`: `∀ x P(x)`. -/
theorem cover (h₁ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fmAt (.ex N C) 1 (var 0))
    (h₂ : ([] : List (Fm PTm 2)) ⊢[PRAAx]
      lt (var 0) (at1 N (var 1)) ⟶ fmAt C 2 (pairT (var 0) (var 1)) ⟶ P.subst ![var 1]) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 P := by
  refine closeUniv 1 ?_
  have h := cover_at C N P h₁ h₂ (Δ := []) (var 0 : PTm 1)
  have e : P.subst ![(var 0 : PTm 1)] = P := by
    have : (![var 0] : Fin 1 → PTm 1) = var := by funext j; fin_cases j; rfl
    rw [this, Fm.subst_id]
  rwa [e] at h

variable (R S : BF) (B D : PTm 1)

/-- `thm:composition`: two bounded searches compose into primitive-recursive witnesses. -/
theorem composition {m : ℕ} {Δ : List (Fm PTm m)}
    (h₁ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fmAt (.ex B R) 1 (var 0))
    (h₂ : ([] : List (Fm PTm 2)) ⊢[PRAAx]
      lt (var 0) (at1 B (var 1)) ⟶ fmAt R 2 (pairT (var 0) (var 1)) ⟶ fmAt (.ex D S) 2 (pairT (var 0) (var 1)))
    (x : PTm m) :
    Δ ⊢[PRAAx] fmAt R m (pairT (bfWit B R x) x) ⋏
      fmAt S m (pairT (bfWit D S (pairT (bfWit B R x) x)) (pairT (bfWit B R x) x)) := by
  have e₁ := inst (Γ := Δ) h₁ ![x]
  rw [fmAt_subst] at e₁
  simp only [Syn.subst_var, Matrix.cons_val_zero] at e₁
  have c := bf_choice B R x e₁
  have e₂ := inst (Γ := Δ) h₂ ![bfWit B R x, x]
  simp only [Fm.subst_imp, subst_lt, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, at1_inst2, fmAt_inst2] at e₂
  have d := bf_choice D S _ (Prf.impE (Prf.impE e₂ (Prf.andE₁ c)) (Prf.andE₂ c))
  exact .andI (Prf.andE₂ c) (Prf.andE₂ d)

end LeanProofs.IPRA.Foundations.BoundedCover
