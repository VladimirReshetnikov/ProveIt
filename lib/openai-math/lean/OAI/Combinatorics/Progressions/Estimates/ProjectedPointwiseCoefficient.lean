/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
import OAI.Combinatorics.Progressions.Polynomial.ShiftedGradedPolynomial

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def gradedPolynomialSymbol :
    VectorPolynomial σ ℚ F.AssociatedGraded →ₗ[ℚ] F.PolynomialSymbol w :=
  (F.polynomialSymbolBasis b ω hlayers w).repr.symm.toLinearMap.comp
    (supportedCoordinates (F.associatedGradedBasis b ω hlayers)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2})

theorem gradedPolynomialSymbol_coordinate
    (p : VectorPolynomial σ ℚ F.AssociatedGraded) (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr (F.gradedPolynomialSymbol b ω hlayers w p) z =
      (F.associatedGradedBasis b ω hlayers).repr (coefficients p z.val.1) z.val.2 := by
  change ((F.polynomialSymbolBasis b ω hlayers w).repr
    ((F.polynomialSymbolBasis b ω hlayers w).repr.symm _)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem gradedPolynomialSymbol_gradedSymbolPolynomial (x : F.PolynomialSymbol w) :
    F.gradedPolynomialSymbol b ω hlayers w (F.gradedSymbolPolynomial b ω hlayers w x) = x := by
  apply (F.polynomialSymbolBasis b ω hlayers w).repr.injective
  ext z
  rw [F.gradedPolynomialSymbol_coordinate, F.gradedSymbolPolynomial_coefficient]

noncomputable def homogeneousSymbolLift (α : σ →₀ ℕ) :
    F.AssociatedGraded →ₗ[ℚ] F.PolynomialSymbol w :=
  (F.gradedPolynomialSymbol b ω hlayers w).comp
    (coefficients.symm.toLinearMap.comp (Finsupp.lsingle α))

@[simp] theorem homogeneousSymbolLift_apply (α : σ →₀ ℕ) (v : F.AssociatedGraded) :
    F.homogeneousSymbolLift b ω hlayers w α v =
      F.gradedPolynomialSymbol b ω hlayers w (monomial α v) := by
  simp only [homogeneousSymbolLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lsingle_apply, coefficients_symm_single]

theorem homogeneousSymbolLift_coordinate [DecidableEq σ] (α : σ →₀ ℕ)
    (v : F.AssociatedGraded) (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr (F.homogeneousSymbolLift b ω hlayers w α v) z =
      if α = z.val.1 then (F.associatedGradedBasis b ω hlayers).repr v z.val.2 else 0 := by
  rw [F.homogeneousSymbolLift_apply, F.gradedPolynomialSymbol_coordinate, coefficients_monomial]
  by_cases h : α = z.val.1 <;> simp [h]

theorem gradedSymbolPolynomial_homogeneousSymbolLift (α : σ →₀ ℕ) (v : F.AssociatedGraded) :
    F.gradedSymbolPolynomial b ω hlayers w (F.homogeneousSymbolLift b ω hlayers w α v) =
      monomial α (basisGradeProjection (F.associatedGradedBasis b ω hlayers) ω (Finsupp.weight w α) v) := by
  classical
  apply coefficients.injective
  ext β
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [coefficients_monomial]
  by_cases hα : α = β
  · subst β
    rw [Finsupp.single_eq_same, basisGradeProjection_repr]
    by_cases hd : Finsupp.weight w α = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(α, i), hd⟩,
        F.homogeneousSymbolLift_coordinate]
      simp only [hd, ite_true]
    · rw [F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ α i hd]
      exact (ite_eq_right (Ne.symm hd)).symm
  · rw [Finsupp.single_eq_of_ne (Ne.symm hα), map_zero, Finsupp.zero_apply]
    by_cases hd : Finsupp.weight w β = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(β, i), hd⟩,
        F.homogeneousSymbolLift_coordinate]
      exact ite_eq_right hα
    · exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ β i hd

theorem homogeneousSymbolLift_coefficient (α : σ →₀ ℕ) (x : F.PolynomialSymbol w) :
    F.homogeneousSymbolLift b ω hlayers w α (coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α) =
      basisCoordinateProjection (F.polynomialSymbolBasis b ω hlayers w) {z | z.val.1 = α} x := by
  classical
  apply (F.polynomialSymbolBasis b ω hlayers w).repr.injective
  ext z
  rw [F.homogeneousSymbolLift_coordinate, basisCoordinateProjection_repr]
  simp only [Set.mem_ofPred_eq]
  by_cases h : z.val.1 = α
  · rw [ite_eq_left h, ite_eq_left h.symm, ← h]
    exact F.gradedSymbolPolynomial_coefficient b ω hlayers w x z
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section Coefficients

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem gradedSymbolPolynomial_coefficient_symbol (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.gradedSymbolPolynomial e ω hF w (F.polynomialSymbolMap w p)) α =
      F.associatedGradedPieceMap (Finsupp.weight w α) ⟨coefficients p.val α, p.property α⟩ := by
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext i
  rw [F.associatedGradedPieceMap_coordinate]
  by_cases hi : Finsupp.weight w α = ω i
  · rw [ite_eq_left hi]
    exact (F.gradedSymbolPolynomial_coefficient e ω hF w _ ⟨(α, i), hi⟩).trans
      (F.polynomialSymbolBasis_repr_map e ω hF w p ⟨(α, i), hi⟩)
  · rw [ite_eq_right hi]
    exact F.gradedSymbolPolynomial_coefficient_of_ne e ω hF w _ α i hi

end Coefficients

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem gradedSymbolPolynomial_filteredMap_coefficient (x : F.PolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (G.gradedSymbolPolynomial f ν hG w (F.filteredPolynomialSymbolMap G φ hφ w x)) α =
      F.associatedGradedMap G φ hφ (coefficients (F.gradedSymbolPolynomial e ω hF w x) α) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.filteredPolynomialSymbolMap_symbol, G.gradedSymbolPolynomial_coefficient_symbol,
    F.gradedSymbolPolynomial_coefficient_symbol, F.associatedGradedMap_piece]
  congr 1
  apply Subtype.ext
  exact F.filteredPolynomialMap_coefficient G φ hφ w p α

theorem gradedSymbolPolynomial_filteredMap (x : F.PolynomialSymbol w) :
    G.gradedSymbolPolynomial f ν hG w (F.filteredPolynomialSymbolMap G φ hφ w x) =
      VectorPolynomial.map (F.associatedGradedMap G φ hφ).toLinearMap
        (F.gradedSymbolPolynomial e ω hF w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α

theorem associatedGradedMap_basis_repr (i : ι) (j : κ) :
    (G.associatedGradedBasis f ν hG).repr
      (F.associatedGradedMap G φ hφ (F.associatedGradedBasis e ω hF i)) j =
      if ω i = ν j then f.repr (φ (e i)) j else 0 := by
  rw [G.associatedGradedBasis_repr, F.associatedGradedBasis_apply]
  change (G.polynomialSymbolBasis f ν hG (fun _ : Unit => 1)).repr
    (F.filteredPolynomialSymbolMap G φ hφ (fun _ : Unit => 1)
      (F.polynomialSymbolBasis e ω hF (fun _ : Unit => 1) _)) _ = _
  rw [F.filteredPolynomialSymbolMap_basis_repr G e ω hF f ν hG φ hφ]
  simp only [unitMonomial_injective.eq_iff]

theorem associatedGradedMap_gradeProjection (j : ℕ) (x : F.AssociatedGraded) :
    F.associatedGradedMap G φ hφ (basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x) =
      basisGradeProjection (G.associatedGradedBasis f ν hG) ν j (F.associatedGradedMap G φ hφ x) := by
  apply basisBlockMap_commutes (F.associatedGradedBasis e ω hF) (G.associatedGradedBasis f ν hG)
    ω ν (F.associatedGradedMap G φ hφ).toLinearMap
  intro i k hik
  change (G.associatedGradedBasis f ν hG).repr
    (F.associatedGradedMap G φ hφ (F.associatedGradedBasis e ω hF i)) k = 0
  rw [F.associatedGradedMap_basis_repr G e ω hF f ν hG φ hφ, ite_eq_right (Ne.symm hik)]

theorem homogeneousSymbolLift_filteredMap (α : σ →₀ ℕ) (x : F.AssociatedGraded) :
    F.filteredPolynomialSymbolMap G φ hφ w (F.homogeneousSymbolLift e ω hF w α x) =
      G.homogeneousSymbolLift f ν hG w α (F.associatedGradedMap G φ hφ x) := by
  apply G.gradedSymbolPolynomial_injective f ν hG w
  rw [F.gradedSymbolPolynomial_filteredMap G e ω hF f ν hG φ hφ w,
    F.gradedSymbolPolynomial_homogeneousSymbolLift, G.gradedSymbolPolynomial_homogeneousSymbolLift,
    VectorPolynomial.map_monomial]
  apply congrArg (monomial α)
  exact F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ (Finsupp.weight w α) x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι M : Type*} [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
  (F : NilpotentLieFiltration M t)

theorem symbol_mem_pointwise_iff_refiltered_coefficients (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w p ∈ F.symbolPointwiseSubalgebra b ω hF w U ↔
      ∀ α, coefficients p.val α ∈ F.gradedRefiltrationLayer U (Finsupp.weight w α) := by
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  apply forall_congr'
  intro α
  rw [F.gradedSymbolPolynomial_coefficient_symbol]
  exact (F.mem_gradedRefiltrationLayer_iff U (Finsupp.weight w α)
    ⟨coefficients p.val α, p.property α⟩).symm

end NilpotentLieFiltration

namespace DegreeRankLieFiltration

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontalSymbolCoefficient_mem (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.PolynomialSymbol w) (hx : x ∈ F.symbolPointwiseSubalgebra b ω hF w U)
    (α : σ →₀ ℕ) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α x ∈
      G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
        (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx)) (Finsupp.weight w α) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  have hcoef := (F.symbol_mem_pointwise_iff_refiltered_coefficients b ω hF w U p).mp hx α
  apply (G.mem_layerHorizontalImage _ _ _ _ _).mpr
  refine ⟨⟨coefficients p.val α, hcoef⟩, ?_⟩
  rw [G.projectedHorizontalSymbolCoefficient_symbol]
  rfl

theorem real_projectedHorizontalSymbolCoefficient_mem (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : ℝ ⊗[ℚ] F.PolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U))
    (α : σ →₀ ℕ) :
    (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ x ∈
      (G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
        (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx))
          (Finsupp.weight w α)).baseChange ℝ := by
  let K := (F.symbolPointwiseSubalgebra b ω hF w U).toSubmodule
  let V := G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
    (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx)) (Finsupp.weight w α)
  let f := G.projectedHorizontalSymbolCoefficient F φ hφ w α
  have hmap : K.map f ≤ V := by
    rintro y ⟨z, hz, rfl⟩
    exact G.projectedHorizontalSymbolCoefficient_mem F φ hφ b ω hF w U z hz α
  apply Submodule.baseChange_mono ℝ hmap
  rw [realification_map]
  exact ⟨x, hx, rfl⟩

end DegreeRankLieFiltration

end Erdos3

end

end OAI
