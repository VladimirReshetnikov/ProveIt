import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

variable {I V R S : Type*} [Fintype I] [CommRing R] [CommRing S]

noncomputable def polynomialCharacterRow (row : I → R) (F : I → MvPolynomial V R) :
    MvPolynomial V R := ∑ i, C (row i) * F i

theorem polynomialCharacterRow_totalDegree_le (row : I → R)
    (F : I → MvPolynomial V R) {d : ℕ} (hF : ∀ i, (F i).totalDegree ≤ d) :
    (polynomialCharacterRow row F).totalDegree ≤ d := by
  unfold polynomialCharacterRow
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simpa using hF i)

theorem polynomialCharacterRow_eval (row : I → R) (F : I → MvPolynomial V R)
    (x : V → R) :
    eval x (polynomialCharacterRow row F) = ∑ i, row i * eval x (F i) := by
  simp only [polynomialCharacterRow, map_sum, map_mul, eval_C]

theorem polynomialCharacterRow_homogeneousComponent (row : I → R)
    (F : I → MvPolynomial V R) (d : ℕ) :
    homogeneousComponent d (polynomialCharacterRow row F) =
      polynomialCharacterRow row (fun i => homogeneousComponent d (F i)) := by
  simp only [polynomialCharacterRow, map_sum, homogeneousComponent_C_mul]

theorem polynomialCharacterRow_map (φ : R →+* S) (row : I → R)
    (F : I → MvPolynomial V R) :
    map φ (polynomialCharacterRow row F) =
      polynomialCharacterRow (fun i => φ (row i)) (fun i => map φ (F i)) := by
  simp only [polynomialCharacterRow, map_sum, map_mul, map_C]

theorem map_homogeneousComponent (φ : R →+* S) (d : ℕ) (P : MvPolynomial V R) :
    map φ (homogeneousComponent d P) = homogeneousComponent d (map φ P) := by
  ext e
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

theorem map_homogeneousComponent_polynomialCharacterRow (φ : R →+* S)
    (row : I → R) (F : I → MvPolynomial V R) (d : ℕ) :
    map φ (homogeneousComponent d (polynomialCharacterRow row F)) =
      ∑ i, C (φ (row i)) * map φ (homogeneousComponent d (F i)) := by
  rw [polynomialCharacterRow_homogeneousComponent, polynomialCharacterRow_map]
  rfl

theorem map_homogeneousComponent_row_sum (φ : R →+* S)
    (row : I → R) (F : I → MvPolynomial V R) (d : ℕ) :
    map φ (homogeneousComponent d (∑ i, C (row i) * F i)) =
      ∑ i, C (φ (row i)) * map φ (homogeneousComponent d (F i)) :=
  map_homogeneousComponent_polynomialCharacterRow φ row F d

end Erdos3

end

end OAI
