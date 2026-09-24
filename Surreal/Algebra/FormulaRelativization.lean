import Mathlib.ModelTheory.Semantics

/-!
# Truth-preserving relativization to a definable embedded structure

The quantifier-relativization argument of `odg:def:cor:arithmetic`.
This explicit recursive transformation works for arbitrary native first-order
formulas and any embedding whose range is defined by a unary formula.
-/

namespace Surreal.FormulaRelativization
open FirstOrder FirstOrder.Language

variable {L : Language} {α : Type*}

/-- Apply a unary guard to any free or in-scope bound variable. -/
def atVariable (δ : L.Formula (Fin 1)) {n : ℕ} (i : α ⊕ Fin n) : L.BoundedFormula α n :=
  BoundedFormula.relabel (fun _ => i) δ

/-- Restrict every quantifier to the unary guard, by structural recursion on the formula. -/
def relativize (δ : L.Formula (Fin 1)) : ∀ {n : ℕ}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t s => .equal t s
  | _, .rel r ts => .rel r ts
  | _, .imp φ ψ => .imp (relativize δ φ) (relativize δ ψ)
  | n, .all φ => ((atVariable δ (Sum.inr (Fin.last n))).imp (relativize δ φ)).all

variable {M N : Type*} [L.Structure M] [L.Structure N]

/-- Relabeling the guard evaluates it at the selected variable, without variable capture. -/
theorem realize_atVariable (δ : L.Formula (Fin 1)) {n : ℕ}
    (i : α ⊕ Fin n) (v : α → N) (xs : Fin n → N) :
    (atVariable δ i).Realize v xs ↔ δ.Realize (fun _ => Sum.elim v xs i) := by
  have he : xs ∘ Fin.natAdd n = (default : Fin 0 → N) := Subsingleton.elim _ _
  simp [atVariable, BoundedFormula.realize_relabel, Formula.Realize, he, Function.comp_def]

/-- Relativized truth in the ambient structure equals truth in the embedded structure. -/
theorem realize_relativize (δ : L.Formula (Fin 1)) (e : M ↪[L] N)
    (hδ : ∀ x : Fin 1 → N, δ.Realize x ↔ ∃ a : M, e a = x 0)
    {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M) :
    (relativize δ φ).Realize (e ∘ v) (e ∘ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [relativize, BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    exact e.injective.eq_iff
  | rel r ts =>
    simp only [relativize, BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    exact e.map_rel r _
  | imp φ ψ ihφ ihψ =>
    simp only [relativize, BoundedFormula.realize_imp, ihφ, ihψ]
  | @all n φ ih =>
    simp only [relativize, BoundedFormula.realize_all, BoundedFormula.realize_imp,
      realize_atVariable, hδ, Sum.elim_inr, Fin.snoc_last]
    constructor
    · intro h a
      have ha := h (e a) ⟨a, rfl⟩
      rw [← Fin.comp_snoc] at ha
      exact (ih _).mp ha
    · intro h b hb
      obtain ⟨a, rfl⟩ := hb
      rw [← Fin.comp_snoc]
      exact (ih _).mpr (h a)

/-- Specialization to formulas with free parameters in the embedded structure. -/
theorem realize_formula (δ : L.Formula (Fin 1)) (e : M ↪[L] N)
    (hδ : ∀ x : Fin 1 → N, δ.Realize x ↔ ∃ a : M, e a = x 0)
    (φ : L.Formula α) (v : α → M) :
    Formula.Realize (relativize δ φ) (e ∘ v) ↔ φ.Realize v := by
  have h := realize_relativize δ e hδ φ v default
  have he : e ∘ (default : Fin 0 → M) = (default : Fin 0 → N) := Subsingleton.elim _ _
  simpa only [he, Formula.Realize] using h

end Surreal.FormulaRelativization
