import TuringDegrees.Structure

/-!
# Representatives of a set Turing degree

Every set degree has infinitely many concrete set representatives.  We make
the representatives explicit by adjoining a computable singleton on the odd
side of the even/odd join.  This is a useful elementary half of the
cardinality discussion on the Turing-degree page; the substantially deeper
continuum-many-degrees theorem is deliberately not smuggled in as an axiom.
-/

noncomputable section

open scoped Computability

namespace TuringDegrees

open scoped SetTuring

/-- A representative of the degree of `A`, tagged by a natural number in a
disjoint, computable half of the join. -/
def taggedRepresentative (A : Set ℕ) (tag : ℕ) : Set ℕ :=
  setJoin A {tag}

theorem singleton_computable (tag : ℕ) :
    ComputablePred (fun n => n ∈ ({tag} : Set ℕ)) := by
  apply PrimrecPred.computablePred
  apply PrimrecPred.of_eq
    (Primrec.eq.comp Primrec.id (Primrec.const tag))
  intro n
  simp [eq_comm]

@[simp]
theorem SetTuringDegree.of_singleton (tag : ℕ) :
    SetTuringDegree.of ({tag} : Set ℕ) = ⊥ :=
  SetTuringDegree.of_eq_bot (singleton_computable tag)

@[simp]
theorem degree_taggedRepresentative (A : Set ℕ) (tag : ℕ) :
    SetTuringDegree.of (taggedRepresentative A tag) = SetTuringDegree.of A := by
  rw [taggedRepresentative, SetTuringDegree.of_join,
    SetTuringDegree.of_singleton, sup_bot_eq]

theorem taggedRepresentative_injective (A : Set ℕ) :
    Function.Injective (taggedRepresentative A) := by
  intro left right equality
  have membershipEquality := congrArg
    (fun S : Set ℕ => oddCode left ∈ S) equality
  simpa [taggedRepresentative] using membershipEquality

/-- Every set Turing degree has an explicit countably infinite family of
pairwise distinct representatives. -/
theorem infinitely_many_representatives (degree : SetTuringDegree) :
    ∃ representatives : ℕ → Set ℕ,
      Function.Injective representatives ∧
      ∀ tag, SetTuringDegree.of (representatives tag) = degree := by
  induction degree using SetTuringDegree.ind_on
  exact ⟨taggedRepresentative _, taggedRepresentative_injective _,
    degree_taggedRepresentative _⟩

end TuringDegrees
