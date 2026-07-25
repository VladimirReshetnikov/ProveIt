import TuringDegrees.Join
import Mathlib.Computability.Reduce

/-!
# The halting degree and computably enumerable degrees

This file isolates the ordinary halting problem as a set of natural numbers,
proves that its degree is strictly above degree zero, and records its standard
many-one completeness for computably enumerable sets.
-/

noncomputable section

open scoped Computability
open Encodable Denumerable
open Nat.Partrec

namespace TuringDegrees

open scoped SetTuring

/-- The ordinary halting problem transported from partial-recursive program
codes to natural numbers by the denumerable coding of `Nat.Partrec.Code`. -/
def haltingSet (n : ℕ) : Prop :=
  (Code.eval (ofNat Code n) 0).Dom

theorem haltingSet_re : REPred haltingSet := by
  exact (ComputablePred.halting_problem_re 0).comp (Computable.ofNat Code)

theorem haltingSet_not_computable : ¬ComputablePred haltingSet := by
  classical
  intro computable
  apply ComputablePred.halting_problem 0
  apply computablePred_iff_computable_decide.mpr
  simpa [haltingSet] using computable.decide.comp (Computable.encode : Computable (encode : Code → ℕ))

namespace SetTuringDegree

/-- `0′`: the degree of the ordinary halting problem. -/
def zeroJump : SetTuringDegree :=
  of {n | haltingSet n}

theorem zeroJump_ne_bot : zeroJump ≠ (⊥ : SetTuringDegree) := by
  intro equality
  exact haltingSet_not_computable (of_eq_bot_iff.mp equality)

/-- The halting degree is strictly above the computable degree. -/
theorem bot_lt_zeroJump : (⊥ : SetTuringDegree) < zeroJump :=
  lt_of_le_of_ne bot_le zeroJump_ne_bot.symm

/-- A degree is computably enumerable when it has a c.e. set representative. -/
def IsComputablyEnumerable (degree : SetTuringDegree) : Prop :=
  ∃ A : Set ℕ, REPred (fun n => n ∈ A) ∧ of A = degree

theorem zeroJump_computablyEnumerable : IsComputablyEnumerable zeroJump :=
  ⟨{n | haltingSet n}, haltingSet_re, rfl⟩

end SetTuringDegree

/-! ## Many-one completeness of the halting problem -/

/-- Every computably enumerable set many-one reduces to the ordinary halting
problem, and every computable preimage of the halting problem is c.e. -/
theorem re_iff_manyOneReducible_haltingSet {A : Set ℕ} :
    REPred (fun n => n ∈ A) ↔
      ManyOneReducible (fun n => n ∈ A) haltingSet := by
  constructor
  · intro enumerable
    let witness : ℕ →. ℕ := fun n =>
      (Part.assert (n ∈ A) fun _ => Part.some ()).map fun _ => 0
    have witnessPartrec : Partrec witness := by
      exact enumerable.map (Computable.const (0 : ℕ)).to₂
    let pairedWitness : ℕ →. ℕ := fun input => witness input.unpair.1
    have pairedWitnessPartrec : Partrec pairedWitness := by
      exact witnessPartrec.comp (Computable.fst.comp Computable.unpair)
    obtain ⟨code, codeSpecification⟩ :=
      Code.exists_code.mp (Partrec.nat_iff.mp pairedWitnessPartrec)
    let reduction : ℕ → ℕ := fun n => encode (Code.curry code n)
    have reductionComputable : Computable reduction := by
      exact (Primrec.encode.comp
        (Code.primrec₂_curry.comp (Primrec.const code) Primrec.id)).to_comp
    refine ⟨reduction, reductionComputable, fun n => ?_⟩
    change n ∈ A ↔ (Code.eval (ofNat Code (encode (Code.curry code n))) 0).Dom
    rw [ofNat_encode, Code.eval_curry, codeSpecification]
    simp [pairedWitness, witness, Part.assert]
  · rintro ⟨reduction, reductionComputable, reductionCorrect⟩
    have composed : REPred (fun n => haltingSet (reduction n)) :=
      haltingSet_re.comp reductionComputable
    exact REPred.of_eq composed fun n => (reductionCorrect n).symm

/-- A many-one reduction is, in particular, a Turing reduction between the
corresponding total characteristic oracles. -/
theorem ManyOneReducible.to_setTuringReducible {A B : Set ℕ}
    (reduction : ManyOneReducible (fun n => n ∈ A) (fun n => n ∈ B)) :
    A ≤ᵀₛ B := by
  obtain ⟨translate, translateComputable, translateCorrect⟩ := reduction
  have queried : RecursiveIn {characteristic B}
      (fun n => characteristic B (translate n)) :=
    recursiveIn_precomp (RecursiveIn.oracle _ (by simp)) translateComputable
  apply queried.of_eq
  intro n
  by_cases hnA : n ∈ A
  · have hnB : translate n ∈ B := (translateCorrect n).mp hnA
    simp [characteristic, hnA, hnB]
  · have hnB : translate n ∉ B := by
      intro membership
      exact hnA ((translateCorrect n).mpr membership)
    simp [characteristic, hnA, hnB]

theorem re_setTuringReducible_haltingSet {A : Set ℕ}
    (enumerable : REPred (fun n => n ∈ A)) :
    A ≤ᵀₛ {n | haltingSet n} :=
  ManyOneReducible.to_setTuringReducible
    (re_iff_manyOneReducible_haltingSet.mp enumerable)

/-- Every computably enumerable degree is below `0′`. -/
theorem SetTuringDegree.computablyEnumerable_le_zeroJump
    {degree : SetTuringDegree}
    (enumerable : SetTuringDegree.IsComputablyEnumerable degree) :
    degree ≤ SetTuringDegree.zeroJump := by
  obtain ⟨A, hA, rfl⟩ := enumerable
  exact re_setTuringReducible_haltingSet hA

end TuringDegrees
