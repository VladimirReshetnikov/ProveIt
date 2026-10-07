import OAI.Combinatorics.Progressions.Fourier.BoundedFrequencyKernel

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def stepOneFrequencyKernel (F : NilpotentLieFiltration L 1) (η : L →ₗ[ℚ] ℚ) :
    LieSubalgebra ℚ L :=
  { LinearMap.ker η with
    lie_mem' := fun {a b} _ _ => by
      change η ⁅a, b⁆ = 0
      rw [F.stepOne_lie_eq_zero, map_zero] }

theorem mem_real_stepOneFrequencyKernel (F : NilpotentLieFiltration L 1) (η : L →ₗ[ℚ] ℚ)
    (x : ℝ ⊗[ℚ] L) :
    x ∈ realificationLieSubalgebra (F.stepOneFrequencyKernel η) ↔ realifyFunctional η x = 0 :=
  mem_realified_frequency_kernel_iff η x

theorem exists_stepOne_linear_splitting {σ ι : Type*} [Fintype σ] [DecidableEq σ]
    (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L)
    (η : L →ₗ[ℚ] ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] L)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (E P R : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      0 < m ∧ m ≤ H ∧ E * P * R = F.realification.linearPolynomialGroup a ∧
      F.PolynomialSlowBound b (fun _ => 1) (fun i => (T i : ℝ)) ((H : ℝ) / (2 * δ)) E ∧
      F.PolynomialRationalGrid b (fun _ => 1) m R ∧
      (∀ t : σ → ℝ, eval₂ t (P.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
        realificationLieSubalgebra (F.stepOneFrequencyKernel η)) ∧
      coefficients (P.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  obtain ⟨m, e, p, r, hm, hmH, hsum, hp, he, hr⟩ :=
    exists_linear_frequency_splitting b η hH hheight T hT a hδ hbias
  let E := F.realification.linearPolynomialGroup e
  let P := F.realification.linearPolynomialGroup p
  let R := F.realification.linearPolynomialGroup r
  refine ⟨m, E, P, R, hm, hmH, ?_, ?_, F.polynomialRationalGrid_linear b m r hr, ?_, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    rw [(F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).stepOne_coord_mul,
      (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).stepOne_coord_mul]
    apply Subtype.ext
    change linearPolynomial e + linearPolynomial p + linearPolynomial r = linearPolynomial a
    rw [← map_add, ← map_add]
    congr 1
    funext i
    exact hsum i
  · apply F.polynomialSlowBound_linear b (fun i => (T i : ℝ)) (fun i => Nat.cast_pos.mpr (hT i))
      (div_nonneg (Nat.cast_nonneg H) (by positivity))
    intro i j
    apply (he i j).trans_eq
    field_simp
  · intro t
    rw [F.mem_real_stepOneFrequencyKernel]
    change realifyFunctional η (eval₂ t (linearPolynomial p)) = 0
    simp only [eval₂_linearPolynomial, map_sum, map_smul, hp, smul_zero, Finset.sum_const_zero]
  · exact coefficients_linearPolynomial_zero p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L)

theorem stepOne_basis_layers (j : ℕ) :
    F.layer j = Submodule.span ℚ (b '' {i | j ≤ (fun _ : ι => 1) i}) := by
  by_cases hj : j ≤ 1
  · have htop : F.layer j = ⊤ := top_unique (F.one_eq_top ▸ F.antitone hj)
    simpa only [hj, Set.ofPred_true, Set.image_univ, b.span_eq] using htop
  · have hbot : F.layer j = ⊥ := bot_unique ((F.antitone (by omega : 2 ≤ j)).trans F.terminal.le)
    simpa only [hj, Set.ofPred_false, Set.image_empty, Submodule.span_empty] using hbot

variable (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include F b hlayers in
theorem stepOne_basis_weight (i : ι) : ω i = 1 := by
  have hpos := F.adaptedBasis_weight_pos b ω hlayers i
  have hle := F.adaptedBasis_weight_le_step b ω hlayers i
  omega

noncomputable def stepOneGradedEquiv : L ≃ₗ⁅ℚ⁆ F.AssociatedGraded :=
  { b.repr.trans (F.associatedGradedBasis b ω hlayers).repr.symm with
  map_lie' {x y} := by
    rw [F.stepOne_lie_eq_zero, F.associatedGradedFiltration.stepOne_lie_eq_zero]
    exact map_zero (b.repr.trans (F.associatedGradedBasis b ω hlayers).repr.symm) }

@[simp] theorem stepOneGradedEquiv_coordinate (x : L) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.stepOneGradedEquiv b ω hlayers x) i =
      b.repr x i := by
  change (F.associatedGradedBasis b ω hlayers).repr
    ((F.associatedGradedBasis b ω hlayers).repr.symm (b.repr x)) i = _
  rw [LinearEquiv.apply_symm_apply]

theorem stepOne_gradedPieceProjection (j : ℕ) (x : L) :
    F.gradedPieceProjection b ω hlayers j x =
      if j = 1 then F.stepOneGradedEquiv b ω hlayers x else 0 := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [F.gradedPieceProjection_coordinate, F.stepOne_basis_weight b ω hlayers i]
  by_cases hj : j = 1
  · simp only [hj, ite_true, F.stepOneGradedEquiv_coordinate]
  · simp only [hj, Ne.symm hj, ite_false, map_zero, Finsupp.zero_apply]

theorem stepOne_graded_submodule (U : Submodule ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U := by
  intro j x hx
  have he : basisGradeProjection (F.associatedGradedBasis b ω hlayers) ω j x =
      if j = 1 then x else 0 := by
    classical
    apply (F.associatedGradedBasis b ω hlayers).repr.injective
    ext i
    rw [basisGradeProjection_repr, F.stepOne_basis_weight b ω hlayers i]
    by_cases hj : j = 1
    · simp only [hj, ite_true]
    · simp only [hj, Ne.symm hj, ite_false, map_zero, Finsupp.zero_apply]
  rw [he]
  split_ifs
  · exact hx
  · exact U.zero_mem

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1)

theorem stepOne_symbol_linearPart (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.polynomialSymbolMap (fun _ => 1)
      (F.linearPolynomialGroup (fun i => coefficients p.val (Finsupp.single i 1))).coord =
      F.polynomialSymbolMap (fun _ => 1) p := by
  have hp : DegreeLE (fun _ : σ => 1) 1 p.val :=
    F.adapted_degreeLE _ ((F.mem_adaptedSubmodule _ _).mp p.property)
  have he : F.adaptedConstant (fun _ : σ => 1) (coefficients p.val 0) +
      (F.linearPolynomialGroup (fun i => coefficients p.val (Finsupp.single i 1))).coord = p := by
    apply Subtype.ext
    exact (eq_affine_of_degreeLE_one p.val hp).symm
  calc
    _ = F.polynomialSymbolMap (fun _ : σ => 1)
        (F.adaptedConstant (fun _ : σ => 1) (coefficients p.val 0) +
          (F.linearPolynomialGroup (fun i => coefficients p.val (Finsupp.single i 1))).coord) := by
      rw [map_add, F.polynomialSymbolMap_constant, zero_add]
    _ = _ := congrArg (F.polynomialSymbolMap (fun _ : σ => 1)) he

end Erdos3.NilpotentLieFiltration

end

end OAI
