/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.AssociatedGradedBasisIndependence

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def shiftedGradedPolynomial (k : ℕ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded where
  toFun p := coefficients.symm (Finsupp.onFinset (coefficients p).support
    (fun α => F.gradedPieceProjection b ω hlayers (Finsupp.weight w α + k) (coefficients p α)) (by
      intro α hα
      apply Finsupp.mem_support_iff.mpr
      intro hc
      apply hα
      rw [hc, map_zero]))
  map_add' p q := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply, map_add, Finsupp.add_apply]
  map_smul' c p := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply, map_smul, Finsupp.smul_apply,
      RingHom.id_apply]

@[simp] theorem shiftedGradedPolynomial_coefficient (k : ℕ) (p : VectorPolynomial σ ℚ L)
    (α : σ →₀ ℕ) :
    coefficients (F.shiftedGradedPolynomial b ω hlayers w k p) α =
      F.gradedPieceProjection b ω hlayers (Finsupp.weight w α + k) (coefficients p α) := by
  simp only [shiftedGradedPolynomial, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply]

theorem shiftedGradedPolynomial_monomial (k : ℕ) (α : σ →₀ ℕ) (v : L) :
    F.shiftedGradedPolynomial b ω hlayers w k (monomial α v) =
      monomial α (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α + k) v) := by
  classical
  apply coefficients.injective
  apply Finsupp.ext
  intro β
  rw [F.shiftedGradedPolynomial_coefficient, coefficients_monomial, coefficients_monomial]
  by_cases h : α = β
  · subst β
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), Finsupp.single_eq_of_ne (Ne.symm h), map_zero]

theorem shiftedGradedPolynomial_coefficient_of_mem (k : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w k) (α : σ →₀ ℕ) :
    coefficients (F.shiftedGradedPolynomial b ω hlayers w k p) α =
      F.associatedGradedPieceMap (Finsupp.weight w α + k) ⟨coefficients p α, hp α⟩ := by
  rw [F.shiftedGradedPolynomial_coefficient]
  exact F.gradedPieceProjection_eq_pieceMap b ω hlayers (Finsupp.weight w α + k)
    ⟨coefficients p α, hp α⟩

theorem shiftedGradedPolynomial_eq_zero_iff (k : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w k) :
    F.shiftedGradedPolynomial b ω hlayers w k p = 0 ↔
      p ∈ F.shiftedAdaptedSubmodule w (k + 1) := by
  constructor
  · intro hz α
    have hc := congrArg (fun q : VectorPolynomial σ ℚ F.AssociatedGraded => coefficients q α) hz
    rw [F.shiftedGradedPolynomial_coefficient_of_mem b ω hlayers w k hp,
      map_zero, Finsupp.zero_apply] at hc
    have hh := (F.associatedGradedPieceMap_eq_zero_iff _ _).mp hc
    simpa only [Nat.add_assoc] using hh
  · intro hp'
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [F.shiftedGradedPolynomial_coefficient_of_mem b ω hlayers w k hp, map_zero, Finsupp.zero_apply]
    apply (F.associatedGradedPieceMap_eq_zero_iff _ _).mpr
    simpa only [Nat.add_assoc] using hp' α

theorem shiftedGradedPolynomial_zero (p : F.adaptedLieSubalgebra w) :
    F.shiftedGradedPolynomial b ω hlayers w 0 p.val =
      F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolMap w p) := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  apply Finsupp.ext
  intro i
  rw [F.shiftedGradedPolynomial_coefficient, Nat.add_zero, F.gradedPieceProjection_coordinate]
  by_cases hd : Finsupp.weight w α = ω i
  · rw [ite_eq_left hd.symm]
    exact ((F.gradedSymbolPolynomial_coefficient b ω hlayers w (F.polynomialSymbolMap w p)
      ⟨(α, i), hd⟩).trans (F.polynomialSymbolBasis_repr_map b ω hlayers w p ⟨(α, i), hd⟩)).symm
  · rw [ite_eq_right (Ne.symm hd)]
    exact (F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ α i hd).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
