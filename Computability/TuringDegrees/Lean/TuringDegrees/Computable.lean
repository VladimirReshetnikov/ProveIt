import TuringDegrees.Basic
import Mathlib.Computability.RE

/-!
# The computable Turing degree

The computable sets form one degree, represented by the empty set.  It is the
least set Turing degree.
-/

noncomputable section

open scoped Classical Computability

namespace TuringDegrees

open scoped SetTuring

/-- The total numerical characteristic function underlying `characteristic`. -/
def characteristicValue (A : Set ℕ) (n : ℕ) : ℕ :=
  if n ∈ A then 1 else 0

@[simp]
theorem characteristic_eq_some_value (A : Set ℕ) :
    characteristic A = fun n => Part.some (characteristicValue A n) :=
  rfl

theorem computable_characteristicValue_iff {A : Set ℕ} :
    Computable (characteristicValue A) ↔ ComputablePred (fun n => n ∈ A) := by
  constructor
  · intro h
    have hp : ComputablePred (fun n => characteristicValue A n = 1) := by
      apply Computable.computablePred
      exact Primrec.eq.decide.to_comp.comp h (Computable.const 1)
    exact hp.of_eq fun n => by
      by_cases hn : n ∈ A <;> simp [characteristicValue, hn]
  · intro h
    classical
    apply (ComputablePred.ite (Computable.const (1 : ℕ))
      (Computable.const (0 : ℕ)) h).of_eq
    intro n
    simp only [characteristicValue]

/-- A set has a partial-recursive characteristic oracle exactly when its
membership predicate is computable. -/
theorem partrec_characteristic_iff {A : Set ℕ} :
    Partrec (characteristic A) ↔ ComputablePred (fun n => n ∈ A) := by
  change Computable (characteristicValue A) ↔ ComputablePred (fun n => n ∈ A)
  exact computable_characteristicValue_iff

theorem computable_set_reducible {A : Set ℕ}
    (hA : ComputablePred (fun n => n ∈ A)) (B : Set ℕ) : A ≤ᵀₛ B :=
  (partrec_characteristic_iff.mpr hA).turingReducible

theorem empty_computable : ComputablePred (fun n => n ∈ (∅ : Set ℕ)) := by
  rw [← computable_characteristicValue_iff]
  apply (Computable.const (0 : ℕ) : Computable fun _ : ℕ => 0).of_eq
  intro n
  simp [characteristicValue]

namespace SetTuringDegree

/-- Degree zero, represented by the empty set. -/
instance instOrderBot : OrderBot SetTuringDegree where
  bot := of ∅
  bot_le degree := by
    induction degree using SetTuringDegree.ind_on
    exact computable_set_reducible empty_computable _

@[simp]
theorem bot_eq : (⊥ : SetTuringDegree) = of ∅ :=
  rfl

/-- A set lies in degree zero exactly when it is computable. -/
@[simp]
theorem of_eq_bot_iff {A : Set ℕ} :
    of A = ⊥ ↔ ComputablePred (fun n => n ∈ A) := by
  constructor
  · intro equality
    have equivalence : A ≡ᵀₛ (∅ : Set ℕ) :=
      of_eq_of.mp (equality.trans bot_eq)
    apply partrec_characteristic_iff.mp
    apply TuringReducible.partrec_of_const (s := Part.some 0)
    have emptyCharacteristic : characteristic (∅ : Set ℕ) = fun _ => Part.some 0 := by
      funext n
      simp [characteristic]
    rw [← emptyCharacteristic]
    exact equivalence.1
  · intro computable
    apply of_eq_of.mpr
    exact ⟨computable_set_reducible computable ∅,
      computable_set_reducible empty_computable A⟩

theorem of_eq_bot {A : Set ℕ} (hA : ComputablePred (fun n => n ∈ A)) :
    of A = ⊥ :=
  of_eq_bot_iff.mpr hA

theorem eq_bot_of_computable_representative {degree : SetTuringDegree}
    {A : Set ℕ} (hdegree : degree = of A)
    (hA : ComputablePred (fun n => n ∈ A)) : degree = ⊥ :=
  hdegree.trans (of_eq_bot hA)

end SetTuringDegree

end TuringDegrees
