import OAI.Combinatorics.Progressions.Linear.ChosenBasisGeometryBounds

namespace OAI

section

namespace Erdos3

def adaptedMarkedMapHeightBudget (p : ℝ) : ℝ :=
  (p + (p + 4) ^ 5 + (p + 2) ^ 4 + 2) ^ 4

theorem exists_adaptedMarkedMapHeightBudget_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → adaptedMarkedMapHeightBudget p ≤ (p + C) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + 4) ^ 5 + (Polynomial.X + 2) ^ 4 + 2) ^ 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, adaptedMarkedMapHeightBudget, Polynomial.eval₂_pow] using hbound p hp

namespace RationalFilteredNilmanifold

open Module

theorem markedMap_basisChange_logHeight
    {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hb : ∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p)
    (hc : ∀ i j, rationalLogHeight (E.basis.repr (c i) j) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p) :
    ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ adaptedMarkedMapHeightBudget p := by
  obtain ⟨_, hinv, _⟩ := E.basis_geometry_of_forward_height c hp hE
    (fun i j => (hc i j).trans (by linarith))
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hD.1
  have he : (Fintype.card (Fin e) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin] using hE.1
  have hnative (i : ι) (j : Fin e) :
      rationalLogHeight (E.basis.repr (φ (b i)) j) ≤ (p + 2) ^ 4 :=
    linearMap_coordinate_logHeight D.basis E.basis φ hp hd hφ (b i) (hb i) j
  let q := p + (p + 4) ^ 5 + (p + 2) ^ 4
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have h5 : 0 ≤ (p + 4) ^ 5 := by positivity
  have h4 : 0 ≤ (p + 2) ^ 4 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hinvq : (p + 4) ^ 5 ≤ q := by dsimp [q]; linarith
  have hnativeq : (p + 2) ^ 4 ≤ q := by dsimp [q]; linarith
  intro i j
  exact linearMap_coordinate_logHeight E.basis c LinearMap.id hq (he.trans hpq)
    (fun a k => (hinv a k).trans hinvq) (φ (b i))
    (fun k => (hnative i k).trans hnativeq) j

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
