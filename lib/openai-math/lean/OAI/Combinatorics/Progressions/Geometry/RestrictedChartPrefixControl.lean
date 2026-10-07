/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Dynamics.RestrictedSymbolGradeIteration
import OAI.Combinatorics.Progressions.Polynomial.MajorPhaseCoordinateDenominator

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

theorem substitute_weightedHomogeneousPart
    {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (w : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ R V) :
    substitute f (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart v d (substitute f p) := by
  induction p using TensorProduct.inductionOn with
  | tmul P x =>
    rw [weightedHomogeneousPart_tmul, substitute_tmul, substitute_tmul,
      weightedHomogeneousPart_tmul, aeval_weightedHomogeneousComponent w v f hf]
  | add p q hp hq => simp only [map_add, hp, hq]

variable {σ τ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem realChartSubstitute_map
    {W : Type*} [AddCommGroup W] [Module ℚ W] [Module ℝ W] [IsScalarTower ℚ ℝ W]
    (f : σ → MvPolynomial τ ℝ) (S : V →ₗ[ℝ] W) (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute f (map (S.restrictScalars ℚ) p) =
      map (S.restrictScalars ℚ) (realChartSubstitute f p) := by
  have hmap : realCoefficientEquiv (map (S.restrictScalars ℚ) p) =
      map S (realCoefficientEquiv p) := by
    apply coefficients.injective
    ext α
    simp only [coefficients_realCoefficientEquiv, coefficients_map,
      LinearMap.restrictScalars_apply]
  have hsymm (q : VectorPolynomial τ ℝ V) :
      realCoefficientEquiv.symm (map S q) =
        map (S.restrictScalars ℚ) (realCoefficientEquiv.symm q) := by
    apply coefficients.injective
    ext α
    simp only [coefficients_realCoefficientEquiv_symm, coefficients_map,
      LinearMap.restrictScalars_apply]
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, hmap, ← map_substitute, hsymm]

theorem realCoefficientEquiv_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ ℚ V) :
    realCoefficientEquiv (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart w d (realCoefficientEquiv p) := by
  apply coefficients.injective
  ext α
  simp only [coefficients_realCoefficientEquiv, coefficients_weightedHomogeneousPart]

theorem realCoefficientEquiv_symm_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ ℝ V) :
    realCoefficientEquiv.symm (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart w d (realCoefficientEquiv.symm p) := by
  apply coefficients.injective
  ext α
  simp only [coefficients_realCoefficientEquiv_symm, coefficients_weightedHomogeneousPart]

theorem realChartSubstitute_weightedHomogeneousPart (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute f (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart v d (realChartSubstitute f p) := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, realCoefficientEquiv_weightedHomogeneousPart,
    substitute_weightedHomogeneousPart w v f hf,
    realCoefficientEquiv_symm_weightedHomogeneousPart]

theorem realChartSubstitute_homogeneous (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ ℚ V)
    (hp : ∀ α, Finsupp.weight w α ≠ d → coefficients p α = 0) :
    ∀ α, Finsupp.weight v α ≠ d → coefficients (realChartSubstitute f p) α = 0 := by
  have he : weightedHomogeneousPart v d (realChartSubstitute f p) =
      realChartSubstitute f p := by
    rw [← realChartSubstitute_weightedHomogeneousPart w v f hf,
      weightedHomogeneousPart_eq_self hp]
  intro α hα
  rw [← he]
  exact weightedHomogeneousPart_homogeneous v d _ α hα

end Erdos3.VectorPolynomial

namespace Erdos3

open MvPolynomial VectorPolynomial

variable {U B : Type*}

theorem normalizedRealPolynomialChart_isWeightedHomogeneous
    (wU : U → ℕ) (wB : B → ℕ) (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ j, (A j).IsWeightedHomogeneous wU (wB j)) (i : U ⊕ B) :
    (normalizedRealPolynomialChart H A i).IsWeightedHomogeneous
      (Sum.elim wU wB) (Sum.elim wU wB i) := by
  cases i with
  | inl i =>
    exact (isWeightedHomogeneous_X (R := ℝ) (Sum.elim wU wB) (Sum.inl i)).C_mul _
  | inr j =>
    apply (isWeightedHomogeneous_X (R := ℝ) (Sum.elim wU wB) (Sum.inr j)).sub
    rw [rename_eq_aeval]
    exact aeval_isWeightedHomogeneous wU (Sum.elim wU wB) (X ∘ Sum.inl)
      (fun i => isWeightedHomogeneous_X (R := ℝ) (Sum.elim wU wB) (Sum.inl i)) (hA j)

theorem normalizedRealPolynomialChart_weightedHomogeneousComponent
    (wU : U → ℕ) (wB : B → ℕ) (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ j, (A j).IsWeightedHomogeneous wU (wB j))
    (d : ℕ) (p : MvPolynomial (U ⊕ B) ℝ) :
    aeval (normalizedRealPolynomialChart H A)
        (weightedHomogeneousComponent (Sum.elim wU wB) d p) =
      weightedHomogeneousComponent (Sum.elim wU wB) d
        (aeval (normalizedRealPolynomialChart H A) p) :=
  aeval_weightedHomogeneousComponent _ _ _
    (normalizedRealPolynomialChart_isWeightedHomogeneous wU wB H A hA) d p

theorem normalizedRealPolynomialChart_weightedHomogeneousPart
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
    (wU : U → ℕ) (wB : B → ℕ) (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ j, (A j).IsWeightedHomogeneous wU (wB j))
    (d : ℕ) (p : VectorPolynomial (U ⊕ B) ℚ V) :
    realChartSubstitute (normalizedRealPolynomialChart H A)
        (weightedHomogeneousPart (Sum.elim wU wB) d p) =
      weightedHomogeneousPart (Sum.elim wU wB) d
        (realChartSubstitute (normalizedRealPolynomialChart H A) p) := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, realCoefficientEquiv_weightedHomogeneousPart,
    substitute_weightedHomogeneousPart (Sum.elim wU wB) (Sum.elim wU wB)
      (normalizedRealPolynomialChart H A)
      (normalizedRealPolynomialChart_isWeightedHomogeneous wU wB H A hA),
    realCoefficientEquiv_symm_weightedHomogeneousPart]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realPolynomialChartSubstitution

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

noncomputable def polynomialChartOuterIteration (F : NilpotentLieFiltration L s)
    (f : σ → MvPolynomial σ ℝ)
    (a r : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) :
    ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot ×
      PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot
  | 0 => (1, 1)
  | n + 1 =>
    let previous := polynomialChartOuterIteration F f a r n
    (previous.1 * realPolynomialChartSubstitution F.realification.lowerCentralSeries_eq_bot f (a n),
      r n * previous.2)

theorem polynomialChartOuterIteration_eq_products (F : NilpotentLieFiltration L s)
    (f : σ → MvPolynomial σ ℝ)
    (a r : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) (n : ℕ) :
    F.polynomialChartOuterIteration f a r n =
      (realPolynomialChartSubstitution F.realification.lowerCentralSeries_eq_bot f
        ((List.range n).map a).prod, ((List.range n).map r).reverse.prod) := by
  induction n with
  | zero => simp only [polynomialChartOuterIteration, List.range_zero, List.map_nil,
      List.prod_nil, List.reverse_nil, map_one]
  | succ n ih =>
    simp only [polynomialChartOuterIteration, ih, List.range_succ, List.map_append,
      List.map_singleton, List.prod_append, List.prod_singleton, List.reverse_append,
      List.reverse_singleton, map_mul]

theorem exists_polynomial_chart_outer_iteration_bounds (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (f : σ → MvPolynomial σ ℝ)
          (q r : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
        (∀ j < s, (q j).coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ j < s, (r j).coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ j < s, CoefficientBound (b.baseChange ℝ) (fun _ => 1)
          (Real.exp ((p + 2) ^ a)) (q j).coord) →
        (∀ j < s, CoefficientGrid (b.baseChange ℝ) l (r j).coord) →
        ∀ n ≤ s, ∃ Echart : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          (F.polynomialChartOuterIteration f q r n).1 =
            realPolynomialChartSubstitution F.realification.lowerCentralSeries_eq_bot f Echart ∧
          CoefficientBound (b.baseChange ℝ) (fun _ => 1)
            (Real.exp ((p + C) ^ C)) Echart.coord ∧
          CoefficientGrid (b.baseChange ℝ) m (F.polynomialChartOuterIteration f q r n).2.coord := by
  obtain ⟨C, hC, hproducts⟩ := exists_outer_polynomial_product_bounds s a s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hproducts F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro f q r hqa hra hqb hrb n hn
  have hmem (v : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
      (g : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
      (hg : g ∈ (List.range n).map v) :
      ∃ j, j < s ∧ v j = g := by
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hg
    exact ⟨j, lt_of_lt_of_le (List.mem_range.mp hj) hn, heq⟩
  obtain ⟨hs, hr⟩ := hprod ((List.range n).map q) ((List.range n).map r)
    (by simpa using hn) (by simpa using hn)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem q g hg; exact hqa j hj)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem r g hg; exact hra j hj)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem q g hg; exact hqb j hj)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem r g hg; exact hrb j hj)
  refine ⟨((List.range n).map q).prod, ?_, hs, ?_⟩
  · rw [F.polynomialChartOuterIteration_eq_products]
  · rw [F.polynomialChartOuterIteration_eq_products]
    exact hr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realPolynomialChartSubstitution

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)
  (U : Submodule ℚ F.AssociatedGraded)
  (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

noncomputable def restrictedMajorChartCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
  ⟨F.homogeneousQuotientGradedPolynomial b ω hF k (S.baseChange ℝ)
    (weightedHomogeneousPart w k p)⟩

@[simp] theorem restrictedMajorChartCorrection_coord (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord =
      F.homogeneousQuotientGradedPolynomial b ω hF k (S.baseChange ℝ)
        (weightedHomogeneousPart w k p) := rfl

theorem restrictedMajorChartCorrection_graded (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w := by
  rw [F.restrictedMajorChartCorrection_coord]
  apply F.homogeneousQuotientGradedPolynomial_graded
  exact weightedHomogeneousPart_homogeneous w k p

theorem restrictedMajorChartCorrection_adapted (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord ∈
      F.associatedGradedFiltration.realification.adaptedLieSubalgebra w :=
  F.associatedGradedFiltration.gradedPolynomial_mem_adapted
    (F.associatedGradedBasis b ω hF) ω (F.associatedGradedFiltration_layer b ω hF) w _
    (F.restrictedMajorChartCorrection_graded b ω hF w U S k p)

theorem restrictedMajorChartCorrection_adapted_one (hw : ∀ i, 0 < w i) (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord ∈
      F.associatedGradedFiltration.realification.adaptedLieSubalgebra (fun _ => 1) := by
  have ha := F.restrictedMajorChartCorrection_adapted b ω hF w U S k p
  intro α
  apply F.associatedGradedFiltration.realification.antitone
    (show Finsupp.weight (fun _ : σ => 1) α ≤ Finsupp.weight w α from ?_) (ha α)
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_one]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right (α i) (hw i))

theorem realGradedSymbolPolynomialHom_restrictedMajorCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.realGradedSymbolPolynomialHom b ω hF w
        (F.restrictedMajorCorrection b ω hF w U S k p) =
      F.restrictedMajorChartCorrection b ω hF w U S k p := by
  apply NilpotentLieBCHGroup.ext
  exact F.realGradedSymbolPolynomial_homogeneousQuotientSymbolLift b ω hF w k
    (S.baseChange ℝ) _ (weightedHomogeneousPart_homogeneous w k p)

theorem restrictedMajorChartCorrection_substitute
    (f : σ → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i)) (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.restrictedMajorChartCorrection b ω hF w U S k (realChartSubstitute f p) =
      realPolynomialChartSubstitution
        F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f
        (F.restrictedMajorChartCorrection b ω hF w U S k p) := by
  apply NilpotentLieBCHGroup.ext
  rw [F.restrictedMajorChartCorrection_coord, realPolynomialChartSubstitution_coord,
    F.restrictedMajorChartCorrection_coord]
  rw [← realChartSubstitute_weightedHomogeneousPart w w f hf]
  simp only [homogeneousQuotientGradedPolynomial, realChartSubstitute_map]

theorem realGradedSymbolPolynomialHom_restrictedMajorCorrection_chart
    (f : σ → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i)) (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.realGradedSymbolPolynomialHom b ω hF w
        (F.restrictedMajorCorrection b ω hF w U S k (realChartSubstitute f p)) =
      realPolynomialChartSubstitution
        F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f
        (F.restrictedMajorChartCorrection b ω hF w U S k p) := by
  rw [F.realGradedSymbolPolynomialHom_restrictedMajorCorrection,
    F.restrictedMajorChartCorrection_substitute b ω hF w U S f hf]

theorem restrictedMajorOuterFactors_chart_representation
    (f : σ → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i))
    (qS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) (n : ℕ) :
    let outer := F.restrictedMajorOuterFactors b ω hF w U S
      (fun j => realChartSubstitute f (qS j)) pR n
    (F.realGradedSymbolPolynomialHom b ω hF w outer.1,
      F.realGradedSymbolPolynomialHom b ω hF w outer.2) =
      F.associatedGradedFiltration.polynomialChartOuterIteration f
        (fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (qS j))
        (fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (pR j)) n := by
  induction n with
  | zero => simp only [restrictedMajorOuterFactors, polynomialChartOuterIteration, map_one]
  | succ n ih =>
    have hleft := congrArg Prod.fst ih
    have hright := congrArg Prod.snd ih
    dsimp only at hleft hright ⊢
    simp only [restrictedMajorOuterFactors, polynomialChartOuterIteration, map_mul,
      F.realGradedSymbolPolynomialHom_restrictedMajorCorrection_chart b ω hF w U S f hf,
      F.realGradedSymbolPolynomialHom_restrictedMajorCorrection, hleft, hright]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_restricted_chart_iteration_bounds (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      ∀ (U : Submodule ℚ F.AssociatedGraded)
        (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
        (eQ : Basis κ ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) (B M : ℝ)
        (qS qP : ℕ), 0 ≤ M → 0 < qS * qP → ((qS * qP : ℕ) : ℝ) ≤ Real.exp p →
      (Fintype.card κ : ℝ) * B * M ≤ Real.exp ((p + 2) ^ a) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i) ∈ realDenominatorGrid qS) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ qS * qP ∣ m ∧
        ∀ (f : σ → MvPolynomial σ ℝ),
        (∀ i, (f i).IsWeightedHomogeneous w (w i)) →
        ∀ pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)),
        (∀ j < s, ∀ α i, |eQ.repr (coefficients (pS j) α) i| ≤ M) →
        (∀ j < s, ∀ α, (fun i => eQ.repr (coefficients (pR j) α) i) ∈ realDenominatorGrid qP) →
        ∀ n ≤ s,
        let outer := F.restrictedMajorOuterFactors b ω hF w U S
          (fun j => realChartSubstitute f (pS j)) pR n
        ∃ Echart : PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
          F.realGradedSymbolPolynomialHom b ω hF w outer.1 =
            realPolynomialChartSubstitution
              F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f Echart ∧
          CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
            (Real.exp ((p + C) ^ C)) Echart.coord ∧
          CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) m
            (F.realGradedSymbolPolynomialHom b ω hF w outer.2).coord := by
  obtain ⟨C, hC, hiteration⟩ := exists_polynomial_chart_outer_iteration_bounds s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hstructure
    U S eQ B M qS qP hM hqpos hqp hcost hSbound hSgrid
  obtain ⟨m, hm, hmp, hqm, hbound⟩ := hiteration F.associatedGradedFiltration
    (F.associatedGradedBasis b ω hF) ω (F.associatedGradedFiltration_layer b ω hF)
    H p hH hp hι hσ hHp hstructure (qS * qP) hqpos hqp
  refine ⟨m, hm, hmp, hqm, ?_⟩
  intro f hf pS pR hpS hpR n hn
  let q := fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (pS j)
  let r := fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (pR j)
  have hslow : ∀ j < s, CoefficientBound
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
        (Real.exp ((p + 2) ^ a)) (q j).coord := by
    intro j hj
    dsimp only [q]
    rw [F.restrictedMajorChartCorrection_coord]
    have hpbase : ∀ α i, |eQ.repr (coefficients (pS j) α) i| ≤
        M / monomialScale (fun _ => 1) α := by
      simpa [monomialScale] using hpS j hj
    have hc := F.homogeneousQuotientGradedPolynomial_coefficientBound b ω hF eQ
      (j + 1) (S.baseChange ℝ) (weightedHomogeneousPart w (j + 1) (pS j))
      (fun _ => 1) (fun _ => zero_lt_one) hM hSbound
      (weightedHomogeneousPart_coordinateBound eQ (fun _ => 1) (fun _ => zero_lt_one)
        hM (pS j) hpbase w (j + 1))
    intro α i
    exact (hc α i).trans (div_le_div_of_nonneg_right hcost
      (monomialScale_pos (fun _ => 1) (fun _ => zero_lt_one) α).le)
  have hgrid : ∀ j < s, CoefficientGrid
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) (qS * qP) (r j).coord := by
    intro j hj
    dsimp only [r]
    rw [F.restrictedMajorChartCorrection_coord]
    apply F.homogeneousQuotientGradedPolynomial_coefficientGrid b ω hF eQ (j + 1)
      (S.baseChange ℝ) (weightedHomogeneousPart w (j + 1) (pR j)) qS qP hSgrid
    exact weightedHomogeneousPart_coordinateGrid eQ (pR j) qP (hpR j hj) w (j + 1)
  obtain ⟨Echart, hE, hEb, hRg⟩ := hbound f q r
    (fun j _ => F.restrictedMajorChartCorrection_adapted_one b ω hF w U S hw (j + 1) (pS j))
    (fun j _ => F.restrictedMajorChartCorrection_adapted_one b ω hF w U S hw (j + 1) (pR j))
    hslow hgrid n hn
  have hrep := F.restrictedMajorOuterFactors_chart_representation b ω hF w U S f hf pS pR n
  have hleft := congrArg Prod.fst hrep
  have hright := congrArg Prod.snd hrep
  dsimp only at hleft hright ⊢
  refine ⟨Echart, hleft.trans hE, hEb, ?_⟩
  rw [hright]
  exact hRg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

section PrefixCongruence

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : Submodule ℚ F.AssociatedGraded)
    (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

theorem restrictedMajorOuterFactors_congr
    (pS pR qS qR : ℕ → VectorPolynomial σ ℚ
      (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (n : ℕ) (hleft : ∀ j < n, pS j = qS j) (hright : ∀ j < n, pR j = qR j) :
    F.restrictedMajorOuterFactors b ω hF w U S pS pR n =
      F.restrictedMajorOuterFactors b ω hF w U S qS qR n := by
  revert hleft hright
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hleft hright
    have hprev := ih
      (fun j hj => hleft j (Nat.lt_succ_of_lt hj))
      (fun j hj => hright j (Nat.lt_succ_of_lt hj))
    simp only [restrictedMajorOuterFactors, hprev,
      hleft n (Nat.lt_succ_self n), hright n (Nat.lt_succ_self n)]

end PrefixCongruence

theorem exists_restricted_chart_prefix_control (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      ∀ (U : Submodule ℚ F.AssociatedGraded)
        (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
        (eQ : Basis κ ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
        (B Bphase : ℝ) (qS : ℕ), 0 ≤ Bphase → 0 < qS →
      (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card κ : ℝ) * Bphase) ≤ Real.exp p →
      (Fintype.card κ : ℝ) * B * Real.exp Bphase ≤ Real.exp ((p + 2) ^ a) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i) ∈ realDenominatorGrid qS) →
      ∀ (f : σ → MvPolynomial σ ℝ),
      (∀ i, (f i).IsWeightedHomogeneous w (w i)) →
      ∀ (pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
        (q : ℕ → ℕ) (n : ℕ), n ≤ s →
      (∀ j < n, 0 < q j) →
      (∀ j < n, (q j : ℝ) ≤ Real.exp ((Fintype.card κ : ℝ) * Bphase)) →
      (∀ j < n, ∀ α i, |eQ.repr (coefficients (pS j) α) i| ≤ Real.exp Bphase) →
      (∀ j < n, ∀ α, (fun i => eQ.repr (coefficients (pR j) α) i) ∈
        realDenominatorGrid (q j)) →
      let outer := F.restrictedMajorOuterFactors b ω hF w U S
        (fun j => realChartSubstitute f (pS j)) pR n
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        qS * (∏ j : Fin n, q j.val) ∣ m ∧
        ∃ Echart : PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
          F.realGradedSymbolPolynomialHom b ω hF w outer.1 =
            realPolynomialChartSubstitution
              F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f Echart ∧
          CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
            (Real.exp ((p + C) ^ C)) Echart.coord ∧
          CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) m
            (F.realGradedSymbolPolynomialHom b ω hF w outer.2).coord := by
  obtain ⟨C, hC, hiteration⟩ := exists_restricted_chart_iteration_bounds s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hstructure
    U S eQ B Bphase qS hBphase hqS hdenbudget hcost hSbound hSgrid f hf
    pS pR q n hn hqpos hqbound hpS hpR
  classical
  let Q : ℕ := ∏ j : Fin n, q j.val
  have hQpos : 0 < Q := majorPhaseCoordinateDenominator_pos
    (fun j : Fin n => q j.val) (fun j => hqpos j.val j.isLt)
  have hQbound : (Q : ℝ) ≤ Real.exp ((s : ℝ) * (Fintype.card κ : ℝ) * Bphase) := by
    have hbase : (Q : ℝ) ≤ Real.exp ((n : ℝ) * (Fintype.card κ : ℝ) * Bphase) := by
      simpa only [Fintype.card_fin, mul_assoc] using
        majorPhaseCoordinateDenominator_le_exp (fun j : Fin n => q j.val)
          ((Fintype.card κ : ℝ) * Bphase) (fun j => hqbound j.val j.isLt)
    apply hbase.trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) (Nat.cast_nonneg _)) hBphase
  have hqQ (j : ℕ) (hj : j < n) : q j ∣ Q :=
    Finset.dvd_prod_of_mem (fun j : Fin n => q j.val) (Finset.mem_univ (⟨j, hj⟩ : Fin n))
  have htotal : ((qS * Q : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hQbound (Nat.cast_nonneg qS)).trans hdenbudget
  obtain ⟨m, hm, hmp, hdiv, hbound⟩ := hiteration F b ω hF w hw H p hH hp hι hσ hHp
    hstructure U S eQ B (Real.exp Bphase) qS Q (Real.exp_nonneg _)
    (Nat.mul_pos hqS hQpos) htotal hcost hSbound hSgrid
  let pS' := fun j => if j < n then pS j else 0
  let pR' := fun j => if j < n then pR j else 0
  have hpS' : ∀ j < s, ∀ α i, |eQ.repr (coefficients (pS' j) α) i| ≤ Real.exp Bphase := by
    intro j _ α i
    by_cases hj : j < n
    · simpa only [pS', ite_eq_left hj] using hpS j hj α i
    · simpa only [pS', ite_eq_right hj, map_zero, Finsupp.zero_apply, abs_zero] using
        Real.exp_nonneg Bphase
  have hpR' : ∀ j < s, ∀ α,
      (fun i => eQ.repr (coefficients (pR' j) α) i) ∈ realDenominatorGrid Q := by
    intro j _ α
    by_cases hj : j < n
    · simpa only [pR', ite_eq_left hj] using
        realDenominatorGrid_subset_of_dvd (hqpos j hj) (hqQ j hj) (hpR j hj α)
    · refine ⟨0, ?_⟩
      funext i
      simp [pR', hj]
  have hprefix : F.restrictedMajorOuterFactors b ω hF w U S
      (fun j => realChartSubstitute f (pS' j)) pR' n =
      F.restrictedMajorOuterFactors b ω hF w U S
        (fun j => realChartSubstitute f (pS j)) pR n := by
    apply F.restrictedMajorOuterFactors_congr
    · intro j hj
      simp only [pS', ite_eq_left hj]
    · intro j hj
      simp only [pR', ite_eq_left hj]
  have hout := hbound f hf pS' pR' hpS' hpR' n hn
  dsimp only at hout ⊢
  rw [hprefix] at hout
  exact ⟨m, hm, hmp, hdiv, hout⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
