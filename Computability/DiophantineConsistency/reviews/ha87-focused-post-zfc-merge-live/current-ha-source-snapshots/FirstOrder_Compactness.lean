/-
  Compactness.lean

  The semantic compactness theorem for the repository's first-order
  language.  A theory is represented extensionally by `Form → Prop`; a
  finite subtheory is represented by a list whose members belong to the
  theory.  Repetitions and order in that list have no semantic effect.

  The hard implication is the standard completeness argument.  A relative
  proof of contradiction from `T` mentions only a finite list of axioms.
  Finite satisfiability and soundness rule out such a proof, and the existing
  Henkin model-existence theorem `model_of_BCon` then supplies a model of all
  of `T`.
-/
import FirstOrder.Completeness

namespace SetTheory.FirstOrderCompactness

open Form

/-- A single nonempty structure and assignment satisfying every member of
`T`.  The assignment itself witnesses that the carrier is nonempty.  For the
sentence theories used by compactness, satisfaction is assignment-independent
by `Sat_sentence_inv`. -/
def TheoryHasModel (T : Form → Prop) : Prop :=
  ∃ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
    ∀ phi, T phi → Sat m v phi

/-- Every finite subtheory of `T`, presented as a list, has a model. -/
def FiniteSubtheoriesHaveModels (T : Form → Prop) : Prop :=
  ∀ G : List Form, (∀ phi, phi ∈ G → T phi) →
    ∃ (Dom : Type) (m : Dom → Dom → Prop) (v : Nat → Dom),
      ∀ phi, phi ∈ G → Sat m v phi

/-- Restricting one model of a theory gives a model of each finite
subtheory. -/
theorem theoryHasModel_finiteSubtheoriesHaveModels {T : Form → Prop}
    (hT : TheoryHasModel T) : FiniteSubtheoriesHaveModels T := by
  rintro G hGT
  obtain ⟨Dom, m, v, hmodel⟩ := hT
  exact ⟨Dom, m, v, fun phi hphi => hmodel phi (hGT phi hphi)⟩

/-- The nontrivial compactness implication: models for all finite
subtheories produce a model of the whole sentence theory. -/
theorem theoryHasModel_of_finiteSubtheoriesHaveModels (T : Form → Prop)
    (hSentences : Sentences T) (hfinite : FiniteSubtheoriesHaveModels T) :
    TheoryHasModel T := by
  have hcon : BCon T [] := by
    rintro ⟨G, hGT, hbot⟩
    obtain ⟨Dom, m, v, hmodel⟩ := hfinite G hGT
    have hbot' : Prov G fBot := by simpa using hbot
    have : Sat m v fBot := soundness hbot' v hmodel
    exact this
  obtain ⟨Dom, m, v, hmodel, _⟩ := model_of_BCon T [] hSentences hcon
  exact ⟨Dom, m, v, hmodel⟩

/-- **First-order compactness theorem.**  A theory of sentences has a model
if and only if every finite subtheory has a model. -/
theorem compactness (T : Form → Prop) (hSentences : Sentences T) :
    TheoryHasModel T ↔ FiniteSubtheoriesHaveModels T :=
  ⟨theoryHasModel_finiteSubtheoriesHaveModels,
   theoryHasModel_of_finiteSubtheoriesHaveModels T hSentences⟩

end SetTheory.FirstOrderCompactness
