import OAI.Combinatorics.Progressions.Linear.MarkedProjectionBounds

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

noncomputable def markedShiftDirectionLinear :
    RationalTorus.Algebra t →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun := markedShiftDirection F v w marked t
  map_add' h k := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (zero_add (0 : VectorPolynomial (Fin t) ℚ L)).symm
    · rfl
  map_smul' a h := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (smul_zero a).symm
    · rfl

noncomputable def markedQuotientDirectionLinear :
    RationalTorus.Algebra t →ₗ[ℚ] MarkedShiftQuotient F v w marked t :=
  (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.comp
    (markedShiftDirectionLinear F v w marked t)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

omit [Fintype ι] in
theorem markedShiftDirection_ambient_height (i : Fin t)
    (j : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (markedShiftDirection F v w marked t (RationalTorus.basis t i)).val j) 1 := by
  rcases j with z | j
  · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
    change RationalHeightLE (b.repr (coefficients (0 : VectorPolynomial (Fin t) ℚ L) z.val.1) z.val.2) 1
    simp only [map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl
  · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
    exact basis_repr_height_one (RationalTorus.basis t) i j

theorem markedShiftDirection_coordinate_height (hω : ∀ i, ω i ≤ s) {H : ℕ} (hH : 1 ≤ H)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) H) (i : Fin t) (j : Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) :
    RationalHeightLE (e.repr (markedShiftDirection F v w marked t (RationalTorus.basis t i)) j)
      ((finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t) + 1) *
        (rationalSolveHeight (finrank ℚ (markedShiftSubalgebra F v w marked t)) H * H) ^
          finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)) := by
  classical
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  have hb := embedding_basis_coordinate_height e (F.associatedDegree.polynomialShiftBasis b ω hF t)
    (markedShiftSubalgebra F v w marked t).incl.toLinearMap
    (fun _ _ h => Subtype.ext h) hH (fun j i => he i j)
    (markedShiftDirection F v w marked t (RationalTorus.basis t i))
    (fun j => (markedShiftDirection_ambient_height F v w marked t b ω hF i j).mono hH) j
  simpa only [Fintype.card_fin,
    ← finrank_eq_card_basis (F.associatedDegree.polynomialShiftBasis b ω hF t)] using hb

theorem markedQuotientDirection_coordinate_height (hω : ∀ i, ω i ≤ s) {H Q q : ℕ} (hH : 1 ≤ H)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) H) (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
    (hf : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)
    (i : Fin t) (j : Fin q) :
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let B := (a + 1) * (rationalSolveHeight d H * H) ^ a
    RationalHeightLE (f.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j)
      ((d + 1) * (B * Q) ^ d) := by
  have hb := linearMap_coordinate_height e f (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (fun j i => hf i j) (markedShiftDirection F v w marked t (RationalTorus.basis t i))
    (markedShiftDirection_coordinate_height F v w marked t b ω hF hω hH e he i) j
  simp only [Fintype.card_fin] at hb
  exact hb

end Erdos3

end

end OAI
