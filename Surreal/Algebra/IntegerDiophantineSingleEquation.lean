import Surreal.Algebra.IntegerDiophantineGuards

/-!
# Combining finite Diophantine systems into one equation

The ordered-ring sum-of-squares clause in the proof of `odg:def:thm:ce`.
The construction retains the witness tuple and introduces no new parameters.
No corresponding assertion is made over unordered fields.
-/

namespace Surreal.IntegerDiophantine
open MvPolynomial
noncomputable section

variable {n : ℕ}

/-- Replace the finite family of equations by its sum of squares. -/
def System.singleEquation (p : System n) : System n where
  witnesses := p.witnesses
  equations := 1
  polynomial _ := ∑ j, p.polynomial j ^ 2

/-- Over an ordered ring, vanishing of the sum of squares is exact simultaneous vanishing. -/
theorem System.holds_singleEquation_iff {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (p : System n) (x : Fin n → R) :
    p.singleEquation.Holds x ↔ p.Holds x := by
  simp only [System.Holds, singleEquation, eval₂_sum, eval₂_pow, Fin.forall_fin_one]
  apply exists_congr
  intro y
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg
    ((p.polynomial j).eval₂ (Int.castRingHom R) (Sum.elim x y)))]
  simp

/-- Every finite-system definition in an ordered ring has a single-equation presentation. -/
theorem Definable.exists_singleEquation {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {D : Set (Fin n → R)} (hD : Definable D) :
    ∃ p : System n, p.equations = 1 ∧ ∀ x, p.Holds x ↔ x ∈ D := by
  obtain ⟨p, hp⟩ := hD
  exact ⟨p.singleEquation, rfl, fun x => (p.holds_singleEquation_iff x).trans (hp x)⟩

end
end Surreal.IntegerDiophantine
