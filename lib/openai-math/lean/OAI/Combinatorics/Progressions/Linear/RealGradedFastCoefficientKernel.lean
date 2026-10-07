/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.GradedUnitEvaluation

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

noncomputable def fastGradedRelativeKernel
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    Submodule ℚ F.squareFiltration.quotientTop.AssociatedGraded :=
  W.toSubmodule ⊓ F.reducedSquareGradedSndMap.ker.toSubmodule

noncomputable def fullFastGradedRelative
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    Submodule ℚ F.AssociatedGraded :=
  (F.fastGradedRelativeKernel W).map (F.reducedSquareGradedDifference e ω hF)

variable (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem firstCoefficientFastSubmodule_graded_coefficients (x : F.FirstCoefficientModule w)
    (hx : x ∈ F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule) :
    ∀ α, coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α ∈
      F.fullFastGradedRelative e ω hF W := by
  rw [F.firstCoefficientFastSubmodule_eq_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  intro α
  rw [F.firstCoefficientGradedPolynomial_reducedSquare_coefficient]
  refine ⟨coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w y) α, ?_, rfl⟩
  constructor
  · exact (F.squareFiltration.quotientTop.mem_symbolPointwiseSubalgebra_iff
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w W y).mp hy.1 α
  · change F.reducedSquareGradedSndMap _ = 0
    rw [F.reducedSquareGradedSnd_coefficient]
    have hz : F.reducedSquareSndSymbolMap w y = 0 := hy.2
    simp only [hz, map_zero, Finsupp.zero_apply]

theorem firstCoefficientFastSubmodule_iff_graded
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) (x : F.FirstCoefficientModule w) :
    x ∈ F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule ↔
      ∀ α, coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α ∈
        F.fullFastGradedRelative e ω hF W := by
  classical
  constructor
  · exact F.firstCoefficientFastSubmodule_graded_coefficients e ω hF w hw W x
  · intro hx
    have hex (α : σ →₀ ℕ) : ∃ y, y ∈ F.fastGradedRelativeKernel W ∧
        F.reducedSquareGradedDifference e ω hF y =
          coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α := hx α
    choose y hy hey using hex
    let q (α : σ →₀ ℕ) : F.FirstCoefficientModule w :=
      F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.homogeneousSymbolLift
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α (y α))
    have hq (α : σ →₀ ℕ) : q α ∈
        F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule := by
      rw [F.firstCoefficientFastSubmodule_eq_image]
      refine ⟨F.squareFiltration.quotientTop.homogeneousSymbolLift
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α (y α), ?_, rfl⟩
      constructor
      · exact F.squareFiltration.quotientTop.homogeneousSymbolLift_mem_pointwise
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w W hW α (y α) (hy α).1
      · change F.reducedSquareSndSymbolMap w _ = 0
        rw [F.reducedSquareSnd_homogeneousSymbolLift]
        have hz : F.reducedSquareGradedSndMap (y α) = 0 := (hy α).2
        rw [hz, map_zero]
    have hp (α : σ →₀ ℕ) : F.firstCoefficientGradedPolynomial e ω hF w (q α) =
        monomial α (coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α) := by
      dsimp only [q]
      rw [F.firstCoefficientGradedPolynomial_reducedSquare_homogeneous, hey,
        F.firstCoefficientGradedPolynomial_homogeneous]
    have he : (∑ α ∈ (coefficients (F.firstCoefficientGradedPolynomial e ω hF w x)).support, q α) = x := by
      apply F.firstCoefficientGradedPolynomial_injective e ω hF w
      rw [map_sum]
      simp_rw [hp]
      exact sum_monomial_coefficients _
    rw [← he]
    exact Submodule.sum_mem _ (fun α _ => hq α)

noncomputable def firstCoefficientGradedQuotientMap :
    F.FirstCoefficientModule w →ₗ[ℚ] VectorPolynomial σ ℚ
      (F.AssociatedGraded ⧸ F.fullFastGradedRelative e ω hF W) :=
  (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ).comp
    (F.firstCoefficientGradedPolynomial e ω hF w)

theorem firstCoefficientFastSubmodule_eq_gradedKernel
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule =
      LinearMap.ker (F.firstCoefficientGradedQuotientMap e ω hF w W) := by
  ext x
  rw [F.firstCoefficientFastSubmodule_iff_graded e ω hF w hw W hW]
  change (∀ α, coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α ∈
    F.fullFastGradedRelative e ω hF W) ↔ F.firstCoefficientGradedQuotientMap e ω hF w W x = 0
  constructor
  · intro hx
    apply coefficients.injective
    ext α
    change coefficients (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ
      (F.firstCoefficientGradedPolynomial e ω hF w x)) α = _
    rw [coefficients_map, map_zero, Finsupp.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hx α)
  · intro hx α
    have hc := congrArg (fun p => coefficients p α) hx
    change coefficients (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ
      (F.firstCoefficientGradedPolynomial e ω hF w x)) α = _ at hc
    rw [coefficients_map, map_zero, Finsupp.zero_apply] at hc
    exact (Submodule.Quotient.mk_eq_zero _).mp hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem realFirstCoefficientGradedQuotient_coefficient (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w)
    (α : σ →₀ ℕ) :
    coefficients (realificationLinearEquiv
      ((F.firstCoefficientGradedQuotientMap e ω hF w W).baseChange ℝ x)) α =
        (F.fullFastGradedRelative e ω hF W).mkQ.baseChange ℝ
          (coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w
            (F.firstCoefficientRealEquiv w x)) α) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, coefficients_realificationLinearEquiv_tmul,
      F.realFirstCoefficientGradedPolynomial_tmul, LinearMap.baseChange_tmul]
    change a ⊗ₜ[ℚ] coefficients (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ
      (F.firstCoefficientGradedPolynomial e ω hF w x)) α = _
    rw [coefficients_map]

theorem realFirstCoefficientFastSubmodule_iff_graded (hw : ∀ i, 0 < w i)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) (x : F.RealFirstCoefficientModule w) :
    x ∈ F.realFirstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule ↔
      ∀ α, coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w x) α ∈
        (F.fullFastGradedRelative e ω hF W).baseChange ℝ := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  have hmem : F.firstCoefficientRealEquiv w y ∈
      F.realFirstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule ↔
      y ∈ (F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule).baseChange ℝ := by
    constructor
    · rintro ⟨z, hz, he⟩
      have hzy : z = y := (F.firstCoefficientRealEquiv w).injective he
      rwa [hzy] at hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [hmem, F.firstCoefficientFastSubmodule_eq_gradedKernel e ω hF w hw W hW, realification_ker]
  change (F.firstCoefficientGradedQuotientMap e ω hF w W).baseChange ℝ y = 0 ↔ _
  rw [realificationLinearEquiv_eq_zero_iff]
  have hker : (F.fullFastGradedRelative e ω hF W).baseChange ℝ =
      LinearMap.ker ((F.fullFastGradedRelative e ω hF W).mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using
      realification_ker (F.fullFastGradedRelative e ω hF W).mkQ
  constructor
  · intro hy α
    rw [hker]
    change (F.fullFastGradedRelative e ω hF W).mkQ.baseChange ℝ _ = 0
    exact (F.realFirstCoefficientGradedQuotient_coefficient e ω hF w W y α).symm.trans (hy α)
  · intro hy α
    have h := hy α
    rw [hker] at h
    exact (F.realFirstCoefficientGradedQuotient_coefficient e ω hF w W y α).trans h

end Erdos3.NilpotentLieFiltration

end

end OAI
