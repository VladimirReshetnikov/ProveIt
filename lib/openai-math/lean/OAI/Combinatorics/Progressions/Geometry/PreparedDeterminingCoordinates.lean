import OAI.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ}

abbrev DeterminingIndex (_L : RankPreparationFamily X J m) (E : Fin m → Type) :=
  Sigma E

abbrev PreparedCoordinate (L : RankPreparationFamily X J m) :=
  (u : Fin m) × (L u).Coord

variable (L : RankPreparationFamily X J m) (E : Fin m → Type)

def determiningWeight (a : L.DeterminingIndex E) : ℕ := a.1.val + 1

theorem determiningWeight_pos (a : L.DeterminingIndex E) :
    1 ≤ L.determiningWeight E a := Nat.le_add_left 1 _

theorem determiningWeight_le (a : L.DeterminingIndex E) :
    L.determiningWeight E a ≤ m := Nat.succ_le_of_lt a.1.isLt

variable {E} [∀ u, Fintype (E u)]
variable [∀ u, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L u).Coord) (euclideanSubspace (L u).space))]
variable (bW : ∀ u, Basis (E u) ℤ
  (latticeSection (standardEuclideanLattice (L u).Coord) (euclideanSubspace (L u).space)))
variable (hmem : ∀ u α, coefficients (L u).poly α ∈ (L u).space)

noncomputable def determiningPolynomial (a : L.DeterminingIndex E) : MvPolynomial X ℝ :=
  integralBasisPolynomialCoordinates (L a.1).space
    ((L a.1).integralCoordinateBasis (bW a.1)) (L a.1).poly (hmem a.1) a.2

noncomputable def determiningMatrix
    (r : L.PreparedCoordinate) (a : L.DeterminingIndex E) : ℤ :=
  if h : a.1 = r.1 then (L r.1).integralCoordinateMatrix (bW r.1) r.2 (h ▸ a.2)
  else 0

omit [∀ u, Fintype (E u)] in
theorem determiningMatrix_same (u : Fin m) (i : (L u).Coord) (e : E u) :
    L.determiningMatrix bW ⟨u, i⟩ ⟨u, e⟩ =
      (L u).integralCoordinateMatrix (bW u) i e := by
  simp [determiningMatrix]

omit [∀ u, Fintype (E u)] in
theorem determiningMatrix_weight (r : L.PreparedCoordinate) (a : L.DeterminingIndex E)
    (hne : L.determiningMatrix bW r a ≠ 0) :
    L.determiningWeight E a = r.1.val + 1 := by
  classical
  by_cases h : a.1 = r.1
  · simp only [determiningWeight, h]
  · simp [determiningMatrix, h] at hne

omit [∀ u, Fintype (E u)] in
theorem determiningPolynomial_degree
    (hdegree : ∀ u, DegreeLE (fun _ => 1) (u.val + 1) (L u).poly)
    (a : L.DeterminingIndex E) :
    (L.determiningPolynomial bW hmem a).totalDegree ≤ L.determiningWeight E a :=
  integralBasisPolynomialCoordinates_totalDegree _ _ _ _ (hdegree a.1) a.2

theorem determiningPolynomial_reconstruction (x : X → ℝ) (r : L.PreparedCoordinate) :
    eval x (L r.1).poly r.2 = ∑ a : L.DeterminingIndex E,
      (L.determiningMatrix bW r a : ℝ) *
        MvPolynomial.eval x (L.determiningPolynomial bW hmem a) := by
  classical
  rw [Fintype.sum_sigma]
  have heq (u : Fin m) :
      (∑ e : E u, (L.determiningMatrix bW r ⟨u, e⟩ : ℝ) *
        MvPolynomial.eval x (L.determiningPolynomial bW hmem ⟨u, e⟩)) =
      if h : u = r.1 then
        ∑ e : E r.1, ((L r.1).integralCoordinateMatrix (bW r.1) r.2 e : ℝ) *
          MvPolynomial.eval x (L.determiningPolynomial bW hmem ⟨r.1, e⟩)
      else 0 := by
    by_cases h : u = r.1
    · subst u
      simp [determiningMatrix]
    · simp [determiningMatrix, h]
  simp_rw [heq]
  rw [Fintype.sum_dite_eq']
  exact eval_integralBasisPolynomialCoordinates (L r.1).space
    ((L r.1).integralCoordinateBasis (bW r.1))
    ((L r.1).integralCoordinateMatrix (bW r.1))
    ((L r.1).integralCoordinateMatrix_cast (bW r.1))
    (L r.1).poly (hmem r.1) x r.2

end Erdos3.RankPreparationFamily

end

end OAI
