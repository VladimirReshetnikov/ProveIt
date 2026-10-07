import Mathlib.Order.UpperLower.Basic
import OAI.Combinatorics.Progressions.Polynomial.TotalDegreeSplitDownsets

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def missingCoordinateBound (s : ℕ) (i j : Fin (s + 1)) : ℕ :=
  if j = i then 0 else s

def missingCoordinateDownset (s : ℕ) (i : Fin (s + 1)) : Set (Fin (s + 1) →₀ ℕ) :=
  {a | ∀ j, a j ≤ missingCoordinateBound s i j}

theorem missingCoordinateBound_le (s : ℕ) (i : Fin (s + 1)) :
    missingCoordinateBound s i ≤ fun _ => s := by
  intro j
  by_cases h : j = i <;> simp [missingCoordinateBound, h]

theorem missingCoordinateDownset_lower (s : ℕ) (i : Fin (s + 1)) :
    IsLowerSet (missingCoordinateDownset s i) :=
  fun _ _ hab hb j => (hab j).trans (hb j)

theorem missingCoordinateDownset_covers (s : ℕ) (a : Fin (s + 1) →₀ ℕ)
    (ha : (∑ j, a j) ≤ s) : ∃ i, a ∈ missingCoordinateDownset s i := by
  classical
  have hall (j : Fin (s + 1)) : a j ≤ s :=
    (Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ j)).trans ha
  have hz : ∃ i, a i = 0 := by
    by_contra hn
    push Not at hn
    have hsum : s + 1 ≤ ∑ i, a i := by
      calc
        _ = ∑ _i : Fin (s + 1), 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (hn i)
    omega
  obtain ⟨i, hi⟩ := hz
  refine ⟨i, fun j => ?_⟩
  by_cases hji : j = i
  · subst j
    simp [missingCoordinateBound, hi]
  · simpa [missingCoordinateBound, hji] using hall j

theorem missingCoordinateDownset_terminal {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (a : Fin (s + 1) →₀ ℕ)
    (ha : ∀ i, a ∉ missingCoordinateDownset s i) :
    (F.totalDegreeMultifiltration (Fin (s + 1))).layer (fun j => a j) = ⊥ := by
  apply F.layer_eq_bot_above_step
  apply Nat.lt_of_not_ge
  intro h
  obtain ⟨i, hi⟩ := missingCoordinateDownset_covers s a h
  exact ha i hi

end Erdos3

end

end OAI
