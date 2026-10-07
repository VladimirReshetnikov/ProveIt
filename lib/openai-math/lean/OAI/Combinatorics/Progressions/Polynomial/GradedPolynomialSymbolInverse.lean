/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
import OAI.Combinatorics.Progressions.Estimates.RealGradedDerivativeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

section General

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedShiftedGradedPolynomial_coefficient (k : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedShiftedGradedPolynomial e ω hF w k x) α =
      (F.gradedPieceProjection e ω hF (Finsupp.weight w α + k)).baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap w x) α) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [F.realAdaptedShiftedGradedPolynomial_tensor, LinearMap.baseChange_tmul,
      realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul,
      F.adaptedShiftedGradedPolynomial_apply, F.shiftedGradedPolynomial_coefficient,
      F.realAdaptedPolynomialMap_coefficient_tmul, LinearMap.baseChange_tmul]

theorem realAdaptedGradedPolynomialLie_coefficient
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF w x) α =
      (F.gradedPieceProjection e ω hF (Finsupp.weight w α)).baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap w x) α) := by
  rw [F.realAdaptedGradedPolynomialLie_apply, F.realAdaptedShiftedGradedPolynomial_coefficient]
  simp only [Nat.add_zero]

theorem realAdaptedGradedPolynomialLie_graded (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie e ω hF w x ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω w := by
  rw [F.realAdaptedGradedPolynomialLie_symbol]
  exact F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule e ω hF w _

theorem realAdaptedGradedPolynomialLie_constant (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF w x) 0 = 0 := by
  rw [F.realAdaptedGradedPolynomialLie_symbol]
  apply ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr.injective
  ext i
  have hi : Finsupp.weight w (0 : σ →₀ ℕ) ≠ ω i := by
    rw [map_zero]
    exact Nat.ne_of_lt (F.adaptedBasis_weight_pos e ω hF i)
  simpa only [map_zero, Finsupp.zero_apply] using
    F.realGradedSymbolPolynomial_coordinate_of_ne e ω hF w
      (realificationLieHom (F.polynomialSymbolMap w) x) 0 i hi

omit w in
theorem realAdaptedGradedPolynomialLie_linear
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (i : σ) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) x)
        (Finsupp.single i 1) =
      (F.layerOneGradedMap e ω hF).baseChange ℝ ((F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) x) (Finsupp.single i 1))) := by
  rw [F.realAdaptedGradedPolynomialLie_coefficient, F.realLayerOneGradedMap_mk]
  simp only [Finsupp.weight_single, one_smul]

omit w in
theorem realAdaptedGradedPolynomialLie_horizontal_mem
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (K : Submodule ℝ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hK : ∀ i, (F.layerOneGradedMap e ω hF).baseChange ℝ ((F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) x) (Finsupp.single i 1))) ∈ K)
    (α : σ →₀ ℕ) :
    basisGradeProjection ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω 1
      (coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) x) α) ∈ K := by
  have hgraded := F.realAdaptedGradedPolynomialLie_graded e ω hF (fun _ : σ => 1) x
  by_cases hα : Finsupp.weight (fun _ : σ => (1 : ℕ)) α = 1
  · obtain hz | ⟨i, rfl⟩ := exponent_of_weight_le_one α hα.le
    · subst α
      simp only [map_zero] at hα
      omega
    · have hg := hgraded (Finsupp.single i 1)
      simp only [Finsupp.weight_single, one_smul, LinearMap.restrictScalars_apply] at hg
      rw [hg, F.realAdaptedGradedPolynomialLie_linear]
      exact hK i
  · have hz := gradedPolynomialSubmodule_projection_homogeneous
      ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω (fun _ : σ => 1) _ hgraded 1 α hα
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at hz
    rw [hz]
    exact K.zero_mem

end General

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem realAdaptedGradedPolynomialLie_fullFast_mem
    (hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W))
    (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) g.val.coord) α ∈
      realificationLieSubalgebra (F.fullFastGradedDiagonal W) := by
  have hg : g.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ : σ => 1)
      (F.fullFastGradedDiagonal W) := by
    rw [F.fullFastPointwise_subgroup_eq e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW]
    exact g.property
  have hs := (F.mem_realPointwisePolynomialSubgroup e ω hF (fun _ => 1)
    (F.fullFastGradedDiagonal W) g.val).mp hg
  have hc := (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ => 1)
    (F.fullFastGradedDiagonal W) _).mp hs α
  rw [F.realAdaptedGradedPolynomialLie_symbol]
  exact hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

section General

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedGradedPolynomialHom_coordinate
    (g : F.RealAdaptedPolynomialGroup w) (α : σ →₀ ℕ) (i : ι) :
    ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
      (coefficients (F.realAdaptedGradedPolynomialHom e ω hF w g).coord α) i =
        if ω i = Finsupp.weight w α then
          (e.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w g.coord) α) i else 0 := by
  change ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
    (coefficients (F.realAdaptedGradedPolynomialLie e ω hF w g.coord) α) i = _
  rw [F.realAdaptedGradedPolynomialLie_coefficient, F.real_gradedPieceProjection_coordinate]

theorem realAdaptedGradedPolynomialHom_bound
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealAdaptedPolynomialGroup w) (hg : F.RealAdaptedCoefficientBound e ω hF w T M g.coord) :
    CoefficientBound ((F.associatedGradedBasis e ω hF).baseChange ℝ) T M
      (F.realAdaptedGradedPolynomialHom e ω hF w g).coord := by
  have hfull := (F.realAdaptedCoefficientBound_iff_formal e ω hF w T hT hM g.coord).mp hg
  intro α i
  rw [F.realAdaptedGradedPolynomialHom_coordinate]
  split_ifs
  · exact hfull α i
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realAdaptedGradedPolynomialHom_grid (l : ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (hg : F.RealAdaptedCoefficientGrid e ω hF w l g.coord) :
    CoefficientGrid ((F.associatedGradedBasis e ω hF).baseChange ℝ) l
      (F.realAdaptedGradedPolynomialHom e ω hF w g).coord := by
  classical
  intro α
  obtain ⟨a, ha⟩ := (F.realAdaptedCoefficientGrid_iff_formal e ω hF w l g.coord).mp hg α
  refine ⟨fun i => if ω i = Finsupp.weight w α then a i else 0, ?_⟩
  funext i
  change ((if ω i = Finsupp.weight w α then a i else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
      (coefficients (F.realAdaptedGradedPolynomialHom e ω hF w g).coord α) i
  rw [F.realAdaptedGradedPolynomialHom_coordinate]
  split_ifs
  · exact congrFun ha i
  · simp only [Int.cast_zero, mul_zero]

end General

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem realAdaptedGradedPolynomialHom_correction
    (hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W)) :
    F.associatedGradedFiltration.FormalCorrectionProperty (F.associatedGradedBasis e ω hF) ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val) :=
  ⟨F.realAdaptedGradedPolynomialLie_fullFast_mem e ω hF W hW g,
    F.realAdaptedGradedPolynomialLie_graded e ω hF (fun _ : σ => 1) g.val.coord,
    F.realAdaptedGradedPolynomialLie_constant e ω hF (fun _ : σ => 1) g.val.coord⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realSymbolOfGradedPolynomial
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) : F.RealPolynomialSymbol w :=
  ((F.polynomialSymbolBasis e ω hF w).baseChange ℝ).repr.symm
    (supportedCoordinates ((F.associatedGradedBasis e ω hF).baseChange ℝ)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2} P)

theorem realSymbolOfGradedPolynomial_coordinate
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis e ω hF w).baseChange ℝ).repr
      (F.realSymbolOfGradedPolynomial e ω hF w P) z =
      ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr (coefficients P z.val.1) z.val.2 := by
  rw [realSymbolOfGradedPolynomial, LinearEquiv.apply_symm_apply]
  rfl

theorem realGradedSymbolPolynomial_ofGradedPolynomial
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : P ∈ gradedPolynomialSubmodule ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω w) :
    F.realGradedSymbolPolynomial e ω hF w (F.realSymbolOfGradedPolynomial e ω hF w P) = P := by
  apply coefficients.injective
  ext α
  apply ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight w α = ω i
  · exact (F.realGradedSymbolPolynomial_coordinate e ω hF w _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfGradedPolynomial_coordinate e ω hF w P ⟨(α, i), h⟩)
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne e ω hF w _ α i h]
    have hi := congrArg (fun v => ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr v i) (hP α)
    simp only [LinearMap.restrictScalars_apply] at hi
    rw [basisGradeProjection_repr, ite_eq_right (Ne.symm h)] at hi
    exact hi

noncomputable def realGradedSymbolPolynomialHom :
    F.RealPolynomialSymbolGroup w →*
      PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.realGradedSymbolPolynomial e ω hF w)

theorem realGradedSymbolPolynomialHom_injective :
    Function.Injective (F.realGradedSymbolPolynomialHom e ω hF w) := by
  intro x y h
  apply NilpotentLieBCHGroup.ext
  apply F.realGradedSymbolPolynomial_injective e ω hF w
  exact congrArg NilpotentLieBCHGroup.coord h

theorem exists_symbol_of_gradedPolynomial
    (P : PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    (hP : P.coord ∈ gradedPolynomialSubmodule ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω w) :
    ∃ x : F.RealPolynomialSymbolGroup w, F.realGradedSymbolPolynomialHom e ω hF w x = P := by
  refine ⟨⟨F.realSymbolOfGradedPolynomial e ω hF w P.coord⟩, ?_⟩
  apply NilpotentLieBCHGroup.ext
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial e ω hF w P.coord hP

theorem realGradedSymbolPolynomialHom_native (g : F.RealAdaptedPolynomialGroup w) :
    F.realGradedSymbolPolynomialHom e ω hF w
      (F.realPolynomialSymbolHom e ω hF w (F.realAdaptedPolynomialGroupHom w g)) =
      F.realAdaptedGradedPolynomialHom e ω hF w g := by
  apply NilpotentLieBCHGroup.ext
  change F.realGradedSymbolPolynomial e ω hF w
    (F.realSymbolOfPolynomial e ω hF w (F.realAdaptedPolynomialMap w g.coord)) = _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  exact (F.realAdaptedGradedPolynomialLie_symbol e ω hF w g.coord).symm

theorem symbolSlowBound_of_gradedPolynomial (T : σ → ℝ) (M : ℝ) (x : F.RealPolynomialSymbolGroup w)
    (hx : CoefficientBound ((F.associatedGradedBasis e ω hF).baseChange ℝ) T M
      (F.realGradedSymbolPolynomialHom e ω hF w x).coord) : F.SymbolSlowBound e ω hF w T M x := by
  intro z
  rw [← F.realGradedSymbolPolynomial_coordinate e ω hF w x.coord z]
  exact hx z.val.1 z.val.2

theorem symbolRationalGrid_of_gradedPolynomial (l : ℕ) (x : F.RealPolynomialSymbolGroup w)
    (hx : CoefficientGrid ((F.associatedGradedBasis e ω hF).baseChange ℝ) l
      (F.realGradedSymbolPolynomialHom e ω hF w x).coord) : F.SymbolRationalGrid e ω hF w l x := by
  choose a ha using hx
  refine ⟨fun z => a z.val.1 z.val.2, ?_⟩
  funext z
  have hz := congrFun (ha z.val.1) z.val.2
  change (a z.val.1 z.val.2 : ℝ) = (l : ℝ) *
    ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial e ω hF w x.coord) z.val.1) z.val.2 at hz
  rw [F.realGradedSymbolPolynomial_coordinate e ω hF w x.coord z] at hz
  exact hz

end Erdos3.NilpotentLieFiltration

end

end OAI
