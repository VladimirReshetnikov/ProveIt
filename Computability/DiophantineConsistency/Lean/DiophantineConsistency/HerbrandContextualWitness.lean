import DiophantineConsistency.HerbrandContextualTreeWitness
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandContextualWitness
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandSchedule HerbrandGeneratedSubmodel HerbrandValuationCompact

/-- A universal side condition survives in the term-generated model, where
failure of every term instance contradicts the asserted existential. -/
theorem no_contextual_countermodel {M : Type} [Structure language M] [Nonempty M]
    (hM : M↓[language] ⊧* UniversalAxiom) (e : ℕ → M)
    (side : Proposition language) (hs : UniversalPrefix side)
    (θ : Semiproposition language 1) (ht : θ.Open)
    (p : UniversalAxiom ⊢ ((∼side) ⋎ (∃⁰ θ)).univCl) :
    ¬(side.Eval ![] e ∧ ∀ t : SyntacticTerm language, ¬(θ/[t]).Eval ![] e) := by
  exact HerbrandContextualTreeWitness.no_contextual_countermodel hM e side
    (HerbrandUniversalTree.prefix_tree side hs) θ ht p
def absent (θ : Semiproposition language 1) (j : ℕ) : Proposition language :=
  ∼(θ/[candidate j])

def failures (side : Proposition language) (θ : Semiproposition language 1) (n : ℕ) : Set (Proposition language) :=
  {φ | φ = side ∨ ∃ j < n, absent θ j = φ}

theorem finite_failure (side : Proposition language) (hs : UniversalPrefix side)
    (θ : Semiproposition language 1) (ht : θ.Open)
    (p : UniversalAxiom ⊢ ((∼side) ⋎ (∃⁰ θ)).univCl) :
    ∃ n, ¬Nonempty (ModelValuation (failures side θ n)) := by
  exact HerbrandContextualTreeWitness.finite_failure side
    (HerbrandUniversalTree.prefix_tree side hs) θ ht p
def termOutput (θ : Semiproposition language 1) : List ℕ → Proposition language
  | [] => ⊥
  | j :: js => (θ/[candidate j]) ⋎ termOutput θ js

private theorem termOutput_eq (θ : Semiproposition language 1) (js : List ℕ) :
    termOutput θ js = HerbrandContextualTreeWitness.termOutput θ js := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [termOutput, HerbrandContextualTreeWitness.termOutput, ih]

theorem output_eval {M : Type} [Structure language M] (θ : Semiproposition language 1)
    (js : List ℕ) (e : ℕ → M) :
    (termOutput θ js).Eval ![] e ↔ ∃ j ∈ js, (θ/[candidate j]).Eval ![] e := by
  simpa only [termOutput_eq] using HerbrandContextualTreeWitness.output_eval θ js e
/-- Finite contextual Herbrand extraction, retaining an existential side
formula `∼side` rather than assuming it false globally. -/
theorem universal_proves_contextual (side : Proposition language) (hs : UniversalPrefix side)
    (θ : Semiproposition language 1) (ht : θ.Open)
    (p : UniversalAxiom ⊢ ((∼side) ⋎ (∃⁰ θ)).univCl) :
    ∃ n, UniversalAxiom ⊢ ((∼side) ⋎ termOutput θ (List.range n)).univCl := by
  simpa only [termOutput_eq] using
    HerbrandContextualTreeWitness.universal_proves_contextual side
      (HerbrandUniversalTree.prefix_tree side hs) θ ht p
end DiophantineConsistency.HerbrandContextualWitness
