import Surreal.Algebra.FormulaRelativization

/-!
# Relativization after a change of language

The natural-arithmetic clause of `odg:def:cor:arithmetic` needs to map the
language of zero, one, addition and multiplication into the ring language
before restricting quantifiers. Its guard may use the richer target language.
-/

namespace Surreal.FormulaRelativization
open FirstOrder FirstOrder.Language

variable {L L' : Language} {α M N : Type*}
    [L.Structure M] [L.Structure N] [L'.Structure N]

/-- A definable-range embedding still interprets all formulas when the guard is expressed
in a larger ambient language. -/
theorem realize_relativize_onBoundedFormula (g : L →ᴸ L') [g.IsExpansionOn N]
    (δ : L'.Formula (Fin 1)) (e : M ↪[L] N)
    (hδ : ∀ x : Fin 1 → N, δ.Realize x ↔ ∃ a : M, e a = x 0)
    {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M) :
    (relativize δ (g.onBoundedFormula φ)).Realize (e ∘ v) (e ∘ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [LHom.onBoundedFormula, Term.bdEqual, relativize, BoundedFormula.Realize,
      LHom.realize_onTerm, ← Sum.comp_elim, HomClass.realize_term]
    exact e.injective.eq_iff
  | rel r ts =>
    simp only [LHom.onBoundedFormula, Relations.boundedFormula, relativize,
      BoundedFormula.Realize, Function.comp_apply, LHom.map_onRelation, LHom.realize_onTerm, ← Sum.comp_elim, HomClass.realize_term]
    exact e.map_rel r _
  | imp φ ψ ihφ ihψ =>
    simp only [LHom.onBoundedFormula, relativize, BoundedFormula.realize_imp, ihφ, ihψ]
  | @all n φ ih =>
    simp only [LHom.onBoundedFormula, relativize, BoundedFormula.realize_all,
      BoundedFormula.realize_imp, realize_atVariable, hδ, Sum.elim_inr, Fin.snoc_last]
    constructor
    · intro h a
      have ha := h (e a) ⟨a, rfl⟩
      rw [← Fin.comp_snoc] at ha
      exact (ih _).mp ha
    · intro h b hb
      obtain ⟨a, rfl⟩ := hb
      rw [← Fin.comp_snoc]
      exact (ih _).mpr (h a)

end Surreal.FormulaRelativization
