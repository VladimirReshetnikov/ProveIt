import OAI.Combinatorics.Progressions.Lattices.PreparedIntegerRemainder

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

namespace VectorPolynomial

theorem ofCoordinates_eq_sum_tmul {X J V : Type*} [Fintype J]
    [AddCommGroup V] [Module ℝ V] (e : Module.Basis J ℝ V)
    (p : J → MvPolynomial X ℝ) :
    ofCoordinates (R := ℝ) e p = ∑ j, p j ⊗ₜ[ℝ] e j := by
  apply coefficients.injective
  ext α
  simp only [coefficients_ofCoordinates, map_sum, Finsupp.finsetSum_apply, coefficients_tmul]

theorem substitute_ofCoordinates {X Y J V : Type*} [Fintype J]
    [AddCommGroup V] [Module ℝ V] (f : X → MvPolynomial Y ℝ)
    (e : Module.Basis J ℝ V) (p : J → MvPolynomial X ℝ) :
    substitute f (ofCoordinates (R := ℝ) e p) =
      ofCoordinates e (fun j => MvPolynomial.aeval f (p j)) := by
  simp only [ofCoordinates_eq_sum_tmul, map_sum, substitute_tmul]

theorem substitute_integerCoordinates {X Y J : Type*} [Fintype J]
    (f : X → MvPolynomial Y ℤ) (ip : J → MvPolynomial X ℤ) :
    substitute (fun i => MvPolynomial.map (Int.castRingHom ℝ) (f i)) (integerCoordinates ip) =
      integerCoordinates (fun j => MvPolynomial.aeval f (ip j)) := by
  rw [integerCoordinates, substitute_ofCoordinates, integerCoordinates]
  congr 1
  funext j
  exact (MvPolynomial.map_bind₁ (Int.castRingHom ℝ) f (ip j)).symm

end VectorPolynomial

namespace RankPreparationLayer

variable {X Y J : Type}

noncomputable def pullback (L : RankPreparationLayer X J) (f : X → MvPolynomial Y ℝ) :
    RankPreparationLayer Y J where
  Coord := L.Coord
  Column := L.Column
  Row := L.Row
  coordFinite := L.coordFinite
  columnFinite := L.columnFinite
  rowFinite := L.rowFinite
  label := L.label
  basis := L.basis
  rows := L.rows
  poly := substitute f L.poly

@[simp] theorem pullback_space (L : RankPreparationLayer X J) (f : X → MvPolynomial Y ℝ) :
    (L.pullback f).space = L.space := rfl

@[simp] theorem pullback_rank (L : RankPreparationLayer X J) (f : X → MvPolynomial Y ℝ) :
    (L.pullback f).rank = L.rank := rfl

theorem Valid.pullback {L : RankPreparationLayer X J} {d H R : ℕ}
    (hL : L.Valid d H R) (f : X → MvPolynomial Y ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (L.pullback f).Valid d H R :=
  ⟨degreeLE_substitute_affine f hf L.poly hL.1,
    coefficients_substitute_mem L.space f L.poly hL.2.1, hL.2.2⟩

end RankPreparationLayer

namespace RankPreparationFamily

variable {X Y J : Type} {m : ℕ}

noncomputable def pullback (L : RankPreparationFamily X J m) (f : X → MvPolynomial Y ℝ) :
    RankPreparationFamily Y J m := fun u => (L u).pullback f

theorem pullback_polynomial [DecidableEq J] (L : RankPreparationFamily X J m)
    (f : X → MvPolynomial Y ℝ) : (L.pullback f).polynomial = substitute f L.polynomial := by
  simp only [polynomial, map_sum, ← map_substitute]
  rfl

theorem pullback_identity [Fintype J] [DecidableEq J] (L : RankPreparationFamily X J m)
    (P E : VectorPolynomial X ℝ (J → ℝ)) (ip : J → MvPolynomial X ℤ) (c : J → ℝ)
    (hP : P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E)
    (f : X → MvPolynomial Y ℤ) :
    let fr := fun i => MvPolynomial.map (Int.castRingHom ℝ) (f i)
    substitute fr P = (L.pullback fr).polynomial +
      integerCoordinates (fun j => MvPolynomial.aeval f (ip j)) + (1 ⊗ₜ[ℝ] c) + substitute fr E := by
  intro fr
  rw [hP, map_add, map_add, map_add, ← pullback_polynomial,
    substitute_integerCoordinates, substitute_tmul, map_one]

end RankPreparationFamily
end Erdos3

end

end OAI
