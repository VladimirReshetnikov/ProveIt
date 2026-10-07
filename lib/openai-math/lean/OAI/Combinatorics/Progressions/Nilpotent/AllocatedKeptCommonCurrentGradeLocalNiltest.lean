import OAI.Combinatorics.Progressions.Dynamics.ActualPathCurrentGradeReset
import OAI.Combinatorics.Progressions.Estimates.AllocatedCommonFrozenSymbolFactors
import OAI.Combinatorics.Progressions.Estimates.AllocatedControlledFrozenPullbacks
import OAI.Combinatorics.Progressions.Estimates.AllocatedProductiveFrozenMajorDetection
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartRecoveredTerminal

namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators TensorProduct

theorem realPolynomialCoefficientGrid_homogeneousComponent {σ : Type*}
    {q : ℕ} {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P)
    (k : ℕ) : realPolynomialCoefficientGrid q (homogeneousComponent k P) := by
  classical
  obtain ⟨z, hz⟩ := hP
  refine ⟨fun α => if α.degree = k then z α else 0, funext fun α => ?_⟩
  change ((if α.degree = k then z α else 0 : ℤ) : ℝ) =
    (q : ℝ) * (homogeneousComponent k P).coeff α
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · exact congrFun hz α
  · simp

theorem homogeneousComponent_scaled_coeff_bound {σ : Type*}
    (P : MvPolynomial σ ℝ) (k : ℕ) (N : σ → ℝ)
    (hN : ∀ i, 0 < N i) (M : ℝ) (hM : 0 ≤ M)
    (hP : ∀ α, |P.coeff α| ≤ M / monomialScale N α) :
    ∀ α, |(homogeneousComponent k P).coeff α| ≤ M / monomialScale N α := by
  intro α
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · exact hP α
  · simpa only [abs_zero] using div_nonneg hM (monomialScale_pos N hN α).le

namespace NilpotentLieFiltration

variable {U ι L : Type*} [Fintype U] [DecidableEq U] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

theorem exists_currentGrade_localMajor_niltest
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (hθW : ∀ x ∈ W, θ x = 0)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : U => 1) W))
    (hE : F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) E₀ =
      F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) E)
    (hR : F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) R =
      F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) R₀)
    (N : U → ℕ) (H m : ℕ) (hm : 0 < m) (M p : ℝ) (hM : 0 ≤ M)
    (hθH : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (hslow : F.SymbolSlowBound b ω hF (fun _ : U => 1)
      (fun i => (N i : ℝ)) M (E₀⁻¹ * E))
    (hgrid : F.SymbolRationalGrid b ω hF (fun _ : U => 1) m (R * R₀⁻¹))
    (hp : 1 ≤ p) (hdim : (Fintype.card U : ℝ) ≤ p)
    (hMexp : (Fintype.card ι : ℝ) * H * M ≤ Real.exp p)
    (hqexp : ((H ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp p)
    (f : (U → ℤ) → ℝ)
    (hN : ∀ i, Real.exp ((p + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ Fintype.card ι * m ∧
      ∃ A : ResidueBoxSlice N q,
        IsDenseCommonStrideBox N ((p + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
        (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
          (𝔼 x ∈ A.integerPoints, f x) ∧
        ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
          T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
          (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
            (Real.fourierChar (eval (fun i => (x i : ℝ))
              (homogeneousComponent (n + 1)
                (F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ
                  (E₀⁻¹ * (E * P * R) * R₀⁻¹)))) : ℂ) *
              star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  have hNpos : ∀ i, 0 < (N i : ℝ) := fun i => (Real.exp_pos _).trans_le (hN i)
  obtain ⟨q, hq, hqbound, hqgrid⟩ :=
    F.scalarSymbolPolynomial_exists_coefficient_grid b ω hF (fun _ : U => 1)
      θ hθH m hm (R * R₀⁻¹) hgrid
  let φ := F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ
    (E₀⁻¹ * (E * P * R) * R₀⁻¹)
  let slow := homogeneousComponent (n + 1)
    (F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ (E₀⁻¹ * E))
  let rat := homogeneousComponent (n + 1)
    (F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ (R * R₀⁻¹))
  have htop : homogeneousComponent (n + 1) (homogeneousComponent (n + 1) φ) =
      slow + rat := by
    rw [homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _)]
    exact F.scalarSymbolPolynomial_homogeneous_normalized_splitting b ω hF θ W hθW
      (n + 1) E P R E₀ R₀ hP hE hR
  have hcap : 0 ≤ (Fintype.card ι : ℝ) * H * M := by positivity
  have hcoeff : ∀ α, |slow.coeff α| ≤
      ((Fintype.card ι : ℝ) * H * M) / monomialScale (fun i => (N i : ℝ)) α :=
    homogeneousComponent_scaled_coeff_bound _ (n + 1) _ hNpos _ hcap
      (F.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF (fun _ : U => 1)
        θ _ hNpos hM hθH (E₀⁻¹ * E) hslow)
  obtain ⟨A, hA, hscore, T, hTnorm, hTbudget, hcorr⟩ :=
    exists_localMajor_dense_slice_niltest_early N q hq
      (homogeneousComponent (n + 1) φ) slow rat
      (homogeneousComponent_isHomogeneous _ _).totalDegree_le
      (homogeneousComponent_isHomogeneous _ _).totalDegree_le htop
      (realPolynomialCoefficientGrid_homogeneousComponent hqgrid (n + 1))
      ((Fintype.card ι : ℝ) * H * M) p hcap hp hdim hMexp
      ((Nat.cast_le.mpr hqbound).trans hqexp) hcoeff f hN
  exact ⟨q, hq, hqbound, A, hA, hscore, T, hTnorm, hTbudget, hcorr⟩

theorem exists_currentGrade_localMajor_niltest_with_lower_phase
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (hθW : ∀ x ∈ W, θ x = 0)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : U => 1) W))
    (hE : F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) E₀ =
      F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) E)
    (hR : F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) R =
      F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) R₀)
    (N : U → ℕ) (H m : ℕ) (hm : 0 < m) (M p : ℝ) (hM : 0 ≤ M)
    (hθH : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (hslow : F.SymbolSlowBound b ω hF (fun _ : U => 1)
      (fun i => (N i : ℝ)) M (E₀⁻¹ * E))
    (hgrid : F.SymbolRationalGrid b ω hF (fun _ : U => 1) m (R * R₀⁻¹))
    (hp : 1 ≤ p) (hdim : (Fintype.card U : ℝ) ≤ p)
    (hMexp : (Fintype.card ι : ℝ) * H * M ≤ Real.exp p)
    (hqexp : ((H ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp p)
    (f : (U → ℤ) → ℝ) (lower : MvPolynomial U ℝ)
    (hlower : lower.totalDegree ≤ n)
    (hN : ∀ i, Real.exp ((p + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ Fintype.card ι * m ∧
      ∃ A : ResidueBoxSlice N q,
        IsDenseCommonStrideBox N ((p + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
        (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
          (𝔼 x ∈ A.integerPoints, f x) ∧
        ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
          T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
          (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
            (Real.fourierChar (eval (fun i => (x i : ℝ))
              (homogeneousComponent (n + 1)
                (F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ
                  (E₀⁻¹ * (E * P * R) * R₀⁻¹)) + lower)) : ℂ) *
              star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  have hNpos : ∀ i, 0 < (N i : ℝ) := fun i => (Real.exp_pos _).trans_le (hN i)
  obtain ⟨q, hq, hqbound, hqgrid⟩ :=
    F.scalarSymbolPolynomial_exists_coefficient_grid b ω hF (fun _ : U => 1)
      θ hθH m hm (R * R₀⁻¹) hgrid
  let φ := F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ
    (E₀⁻¹ * (E * P * R) * R₀⁻¹)
  let slow := homogeneousComponent (n + 1)
    (F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ (E₀⁻¹ * E))
  let rat := homogeneousComponent (n + 1)
    (F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ (R * R₀⁻¹))
  have htop : homogeneousComponent (n + 1) (homogeneousComponent (n + 1) φ + lower) =
      slow + rat := by
    rw [map_add, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _),
      homogeneousComponent_eq_zero _ lower (by omega), add_zero]
    exact F.scalarSymbolPolynomial_homogeneous_normalized_splitting b ω hF θ W hθW
      (n + 1) E P R E₀ R₀ hP hE hR
  have hcap : 0 ≤ (Fintype.card ι : ℝ) * H * M := by positivity
  have hcoeff : ∀ α, |slow.coeff α| ≤
      ((Fintype.card ι : ℝ) * H * M) / monomialScale (fun i => (N i : ℝ)) α :=
    homogeneousComponent_scaled_coeff_bound _ (n + 1) _ hNpos _ hcap
      (F.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF (fun _ : U => 1)
        θ _ hNpos hM hθH (E₀⁻¹ * E) hslow)
  obtain ⟨A, hA, hscore, T, hTnorm, hTbudget, hcorr⟩ :=
    exists_localMajor_dense_slice_niltest_early N q hq
      (homogeneousComponent (n + 1) φ + lower) slow rat
      ((totalDegree_add _ _).trans (max_le
        (homogeneousComponent_isHomogeneous _ _).totalDegree_le (hlower.trans (Nat.le_succ n))))
      (homogeneousComponent_isHomogeneous _ _).totalDegree_le htop
      (realPolynomialCoefficientGrid_homogeneousComponent hqgrid (n + 1))
      ((Fintype.card ι : ℝ) * H * M) p hcap hp hdim hMexp
      ((Nat.cast_le.mpr hqbound).trans hqexp) hcoeff f hN
  exact ⟨q, hq, hqbound, A, hA, hscore, T, hTnorm, hTbudget, hcorr⟩

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem exists_actual_path_current_grade_local_niltest (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {τ ι κ L : Type*} [Fintype τ] [DecidableEq τ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card τ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ N : τ → ℕ, (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ {n : ℕ}
          [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)], n ≤ s →
        ∀ (U : LieSubalgebra ℚ F.AssociatedGraded)
          (vg : κ → F.PolynomialSymbol (fun _ : τ => 1)),
        Submodule.span ℚ (Set.range vg) =
          (F.symbolPointwiseSubalgebra b ω hF (fun _ : τ => 1) U).toSubmodule →
        (∀ i z, RationalHeightLE
          ((F.polynomialSymbolBasis b ω hF (fun _ : τ => 1)).repr (vg i) z) H) →
        ∀ {σ : Type*} (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ),
        ∀ hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i),
        ∀ K : Set (σ → ℝ),
        (∀ u : τ → ℝ,
          (fun i => MvPolynomial.eval u
            (weightedHomogeneousComponent (fun _ : τ => 1) (w i) (β i))) ∈ K) →
        ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
          (E R : F.RealPolynomialSymbolGroup w),
        (∀ t ∈ K, ∀ j < n + 1, F.realSymbolGradeEvaluation b ω hF w j t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈ realificationLieSubalgebra U) →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1)
          (fun i => weightedHomogeneousComponent (fun _ : τ => 1) (w i) (β i))
          (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        ∀ (El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : τ => 1)),
        El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ : τ => 1)
          (F.weightedAdaptedRealChartHom w (fun _ : τ => 1) β hβ g) →
        Pl.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra b ω hF (fun _ : τ => 1) U) →
        F.SymbolSlowBound b ω hF (fun _ : τ => 1) (fun i => (N i : ℝ))
          (Real.exp ((p + 2) ^ a)) El →
        F.SymbolSlowBound b ω hF (fun _ : τ => 1) (fun i => (N i : ℝ))
          (Real.exp ((p + 2) ^ a)) (pull E) →
        F.SymbolRationalGrid b ω hF (fun _ : τ => 1) l Rl →
        F.SymbolRationalGrid b ω hF (fun _ : τ => 1) l (pull R) →
        ∀ (θ : F.AssociatedGraded →ₗ[ℚ] ℚ), (∀ x ∈ U, θ x = 0) →
        ∀ (Hθ : ℕ) (pLocal : ℝ),
        (∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) Hθ) →
        1 ≤ pLocal → (Fintype.card τ : ℝ) ≤ pLocal →
        (Fintype.card ι : ℝ) * Hθ * Real.exp ((p + C) ^ C) ≤ Real.exp pLocal →
        ((Hθ ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp pLocal →
        ∀ (score : (τ → ℤ) → ℝ) (lower : MvPolynomial τ ℝ), lower.totalDegree ≤ n →
        (∀ i, Real.exp ((pLocal + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * m ∧
          ∃ A : ResidueBoxSlice N q,
            IsDenseCommonStrideBox N ((pLocal + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
            (𝔼 x : (∀ i, Fin (N i)), score (fun i => ((x i).val : ℤ))) ≤
              (𝔼 x ∈ A.integerPoints, score x) ∧
            ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : τ => 1),
              T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
              (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
                (Real.fourierChar (eval (fun i => (x i : ℝ))
                  (homogeneousComponent (n + 1)
                    (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) θ
                      ((pull E)⁻¹ * F.realPolynomialSymbolHom b ω hF (fun _ : τ => 1)
                        (F.weightedAdaptedRealChartHom w (fun _ : τ => 1) β hβ g) *
                          (pull R)⁻¹)) + lower)) : ℂ) *
                  star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  obtain ⟨C, hC, hreset⟩ := exists_actual_path_current_grade_reset s a
  refine ⟨C, hC, ?_⟩
  intro τ ι κ L _ _ _ _ _ _ F b ω hF H l p hH hl hp hι hτ hκ hHp hlp hb N hN
  obtain ⟨m, hm, hmp, hlm, hresetm⟩ := hreset F b ω hF (fun _ : τ => 1)
    (fun _ => Nat.zero_lt_one) H l p hH hl hp hι hτ hκ hHp hlp hb (fun i => (N i : ℝ)) hN
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro n _ _ _ _ hn U vg hspan hvg σ w β hβ K hK g E R hx
  dsimp only
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1)
    (fun i => weightedHomogeneousComponent (fun _ : τ => 1) (w i) (β i))
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  intro El Pl Rl hlocal hPl hEl hE hRl hR θ hθ Hθ pLocal hθH hpLocal hdimLocal
    hMexp hqexp score lower hlower hNLocal
  obtain ⟨E', P', R', hprod, hP', hE', hR', _, _, hslowdiff, hgriddiff⟩ :=
    hresetm U vg hspan hvg w β hβ K hK g E R (n + 1) (Nat.add_le_add_right hn 1)
      hx El Pl Rl hlocal hPl hEl hE hRl hR
  have htest := F.exists_currentGrade_localMajor_niltest_with_lower_phase b ω hF U θ hθ
    E' P' R' (pull E) (pull R) hP' hE' hR' N Hθ m hm
    (Real.exp ((p + C) ^ C)) pLocal (Real.exp_nonneg _) hθH hslowdiff hgriddiff
    hpLocal hdimLocal hMexp hqexp score lower hlower hNLocal
  rw [hprod] at htest
  exact htest

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem exists_actual_path_buffered_localMajor_niltest (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {τ ι κ L : Type*} [Fintype τ] [DecidableEq τ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card τ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ N : τ → ℕ, (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ {n : ℕ}
          [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)], n ≤ s →
        ∀ (U : LieSubalgebra ℚ F.AssociatedGraded)
          (vg : κ → F.PolynomialSymbol (fun _ : τ => 1)),
        Submodule.span ℚ (Set.range vg) =
          (F.symbolPointwiseSubalgebra b ω hF (fun _ : τ => 1) U).toSubmodule →
        (∀ i z, RationalHeightLE
          ((F.polynomialSymbolBasis b ω hF (fun _ : τ => 1)).repr (vg i) z) H) →
        ∀ {mTag : ℕ} {X η : Type} (J : Fin mTag → Type) [∀ j, Fintype (J j)]
          (eQ : Basis η ℚ (F.AssociatedGraded ⧸ U.toSubmodule)) (j : η)
          (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (c : Fin (Fintype.card (LowTaggedIndex J (n + 1))) → ℝ)
          (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ),
        ∀ hβ : ∀ i, integerSampledRealChart β i ∈
          weightedSupportLE (fun _ : τ => 1) (fullTaggedVariableWeight J i),
        ∀ K : Set ((X ⊕ (Σ j, J j)) → ℝ),
        (∀ u : τ → ℝ, (fun i => MvPolynomial.eval u
          (homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))) ∈ K) →
        ∀ (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group)
          (E R : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)),
        (∀ t ∈ K, ∀ d < n + 1,
          F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) d t
            (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord ∈
              realificationLieSubalgebra U) →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
          (fun _ : τ => 1)
          (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
          (fun i => sampledTopPhase_coordinate_homogeneous
            (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
        ∀ (El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : τ => 1)),
        El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ : τ => 1)
          (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : τ => 1)
            (integerSampledRealChart β) hβ g) →
        Pl.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra b ω hF (fun _ : τ => 1) U) →
        F.SymbolSlowBound b ω hF (fun _ : τ => 1) (fun i => (N i : ℝ))
          (Real.exp ((p + 2) ^ a)) El →
        F.SymbolSlowBound b ω hF (fun _ : τ => 1) (fun i => (N i : ℝ))
          (Real.exp ((p + 2) ^ a)) (pull E) →
        F.SymbolRationalGrid b ω hF (fun _ : τ => 1) l Rl →
        F.SymbolRationalGrid b ω hF (fun _ : τ => 1) l (pull R) →
        ∀ (Hθ : ℕ) (pLocal : ℝ),
        (∀ i, RationalHeightLE (((eQ.coord j).comp U.toSubmodule.mkQ)
          (F.associatedGradedBasis b ω hF i)) Hθ) →
        1 ≤ pLocal → (Fintype.card τ : ℝ) ≤ pLocal →
        (Fintype.card ι : ℝ) * Hθ * Real.exp ((p + C) ^ C) ≤ Real.exp pLocal →
        ((Hθ ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp pLocal →
        ∀ score : (τ → ℤ) → ℝ,
        (∀ i, Real.exp ((pLocal + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) →
        (∀ u ∈ integerBox N, ∀ i,
          |MvPolynomial.eval (fun x => (integerSampledSpatial β u x : ℝ))
            (lowTaggedPolynomial J (n + 1) poly i) - c i -
              (integerSampledLowTags J (n + 1) β u i : ℝ)| ≤ 1 / 8) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * m ∧
          ∃ A : ResidueBoxSlice N q,
            IsDenseCommonStrideBox N ((pLocal + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
            (𝔼 x : (∀ i, Fin (N i)), score (fun i => ((x i).val : ℤ))) ≤
              (𝔼 x ∈ A.integerPoints, score x) ∧
            ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : τ => 1),
              T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
              (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
                majorPhasePlateauSignal J (n + 1) poly c
                  (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
                    (lowTaggedVectorRestrict J (n + 1)
                      (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
                        U.toSubmodule (n + 1)
                        (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
                  (integerSampledSpatial β x) *
                    star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  obtain ⟨C, hC, htest⟩ := exists_actual_path_current_grade_local_niltest s a
  refine ⟨C, hC, ?_⟩
  intro τ ι κ L _ _ _ _ _ _ F b ω hF H l p hH hl hp hι hτ hκ hHp hlp hb N hN
  obtain ⟨m, hm, hmp, hlm, htestm⟩ := htest F b ω hF H l p
    hH hl hp hι hτ hκ hHp hlp hb N hN
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro n _ _ _ _ hn U vg hspan hvg mTag X η J _ eQ j poly c β hβ K hK g E R hx
  dsimp only
  intro El Pl Rl hlocal hPl hEl hE hRl hR Hθ pLocal hθH hpLocal hdimLocal
    hMexp hqexp score hNLocal hbuffer
  obtain ⟨lower, hlower, hphase⟩ := F.exists_bufferedSampledCurrentGrade_phase
    b ω hF J β hβ U.toSubmodule eQ j n
    (F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g) E R poly c
  have hθ : ∀ x ∈ U, ((eQ.coord j).comp U.toSubmodule.mkQ) x = 0 :=
    fun x hx => F.quotientFunctional_kills_fast U.toSubmodule (eQ.coord j) x hx
  obtain ⟨q, hq, hqbound, A, hAdense, hscore, T, hTnorm, hTcomplexity, hcorr⟩ :=
    htestm hn U vg hspan hvg (fullTaggedVariableWeight J) (integerSampledRealChart β)
      hβ K hK g E R hx El Pl Rl hlocal hPl hEl hE hRl hR
      ((eQ.coord j).comp U.toSubmodule.mkQ) hθ Hθ pLocal hθH hpLocal hdimLocal
      hMexp hqexp score lower hlower hNLocal
  refine ⟨q, hq, hqbound, A, hAdense, hscore, T, hTnorm, hTcomplexity, ?_⟩
  have hactual := F.realPolynomialSymbolHom_weightedAdaptedRealChart b ω hF
    (fullTaggedVariableWeight J) (fun _ : τ => 1) (integerSampledRealChart β) hβ g
  have hinside (u : τ → ℤ) (hu : u ∈ A.integerPoints) : u ∈ integerBox N := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    apply (mem_integerBox N _).mpr
    intro i
    refine ⟨Int.natCast_nonneg _, ?_⟩
    change ((A.point t i).val : ℤ) < (N i : ℤ)
    exact_mod_cast (A.point t i).isLt
  have heq : (𝔼 x ∈ A.integerPoints,
      majorPhasePlateauSignal J (n + 1) poly c
        (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J (n + 1)
            (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
              U.toSubmodule (n + 1)
              (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
        (integerSampledSpatial β x) *
          star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))) =
      (𝔼 x ∈ A.integerPoints,
        (Real.fourierChar (eval (fun i => (x i : ℝ))
          (homogeneousComponent (n + 1)
            (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1)
              ((eQ.coord j).comp U.toSubmodule.mkQ)
              ((F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
                (fun _ : τ => 1)
                (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
                (fun i => sampledTopPhase_coordinate_homogeneous
                  (fullTaggedVariableWeight J i) (integerSampledRealChart β i)) E)⁻¹ *
                F.realPolynomialSymbolHom b ω hF (fun _ : τ => 1)
                  (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : τ => 1)
                    (integerSampledRealChart β) hβ g) *
                (F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
                  (fun _ : τ => 1)
                  (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
                  (fun i => sampledTopPhase_coordinate_homogeneous
                    (fullTaggedVariableWeight J i) (integerSampledRealChart β i)) R)⁻¹)) + lower)) : ℂ) *
          star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))) := by
    apply Finset.expect_congr rfl
    intro x hxA
    have h := hphase x (hbuffer x (hinside x hxA))
    rw [hactual]
    exact congrArg (fun z : ℂ => z *
      star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))) h
  rw [heq]
  exact hcorr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped TensorProduct BigOperators Classical

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

noncomputable def allocatedFrozenCurrentGradeResetConstant (s a : ℕ) : ℕ :=
  Classical.choose (exists_actual_path_buffered_localMajor_niltest.{0, 0, 0, 0} s a)

theorem allocatedFrozenCurrentGradeResetConstant_ge_two (s a : ℕ) :
    2 ≤ allocatedFrozenCurrentGradeResetConstant s a := by
  unfold allocatedFrozenCurrentGradeResetConstant
  with_reducible exact
    (Classical.choose_spec (exists_actual_path_buffered_localMajor_niltest.{0, 0, 0, 0} s a)).1

variable {mTag : ℕ} {G X : Type} [Fintype G] {I Deck J : Fin mTag → Type}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin mTag → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
variable (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (Utag j)))
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
variable {Rad σ : Fin mTag → ℝ} (S : LayerSamplerScale (G := G) B Utag btag Rad σ)
variable (hRad : ∀ j, 0 < Rad j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)

theorem exists_allocated_frozen_current_grade_local_niltest (s a : ℕ)
    (keep : LayerSamplerVariables G I n B → Prop)
    {ι κ L : Type} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H l : ℕ) (p : ℝ) (hH : 1 ≤ H) (hl : 0 < l) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hτ : (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    (hN : ∀ i : {i : LayerSamplerVariables G I n B // keep i},
      Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ≤
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val : ℕ) : ℝ)) :
    ∃ reset : ℕ, 0 < reset ∧
      (reset : ℝ) ≤ Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ∧ l ∣ reset ∧
      ∀ {r : ℕ}
        [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)], r ≤ s →
      ∀ (fast : LieSubalgebra ℚ F.AssociatedGraded)
        (vg : κ → F.PolynomialSymbol (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      Submodule.span ℚ (Set.range vg) =
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast).toSubmodule →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)).repr (vg i) z) H) →
      ∀ {η : Type} (eQ : Basis η ℚ (F.AssociatedGraded ⧸ fast.toSubmodule)) (j : η)
        (c : ∀ j, Utag j) (origin : X → ℤ)
        (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
        (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ),
      AllocatedCenteredFramedRecoveredSampleAt B Utag btag hbtag otag S hRad hσ poly hm c origin v sample read →
      ∀ (fixed : {i : LayerSamplerVariables G I n B // ¬keep i} → ℤ),
      (∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val) →
      (∀ j, σ j ≤ 1) →
      ∀ (Cgeo : Fin mTag → ℝ), (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (Utag j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8) →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      ∀ (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (Bstage pK M LongSide : ℝ) (blocks : ℕ),
      RationalTaggedConstraintCertificate J Set.univ K Bstage blocks →
      (∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      0 ≤ pK → Bstage ≤ pK → (∀ j, (Fintype.card (J j) : ℝ) ≤ pK) →
      0 ≤ M → (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ M) →
      1 ≤ LongSide →
      (∀ i, keep i → LongSide ≤ layerSamplerBox B Utag btag S i) →
      Real.exp ((pK + 2) ^ 9) ^ 2 * M < LongSide →
      let β := allocatedFrozenIntegerFullChart B Utag btag otag poly hm c origin v sample keep fixed
      let N := fun i : {i : LayerSamplerVariables G I n B // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val
      ∀ (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group)
        (E R : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)),
      (∀ t ∈ K, ∀ d < r + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) d t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord ∈
            realificationLieSubalgebra fast) →
      let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
        (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
      ∀ (El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
          (integerSampledRealChart β)
          (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm c origin v sample keep fixed) g) →
      Pl.coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast) →
      F.SymbolSlowBound b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => (N i : ℝ)) (Real.exp ((p + 2) ^ a)) El →
      F.SymbolSlowBound b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => (N i : ℝ)) (Real.exp ((p + 2) ^ a)) (pull E) →
      F.SymbolRationalGrid b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) l Rl →
      F.SymbolRationalGrid b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) l (pull R) →
      ∀ (Hθ : ℕ) (pLocal : ℝ),
      (∀ i, RationalHeightLE (((eQ.coord j).comp fast.toSubmodule.mkQ)
        (F.associatedGradedBasis b ω hF i)) Hθ) →
      1 ≤ pLocal → (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ pLocal →
      (Fintype.card ι : ℝ) * Hθ *
        Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
          allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal →
      ((Hθ ^ Fintype.card ι * reset : ℕ) : ℝ) ≤ Real.exp pLocal →
      ∀ score : ({i : LayerSamplerVariables G I n B // keep i} → ℤ) → ℝ,
      (∀ i, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (N i : ℝ)) →
      ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * reset ∧
        ∃ A : ResidueBoxSlice N q,
          IsDenseCommonStrideBox N ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) A.integerPoints ∧
          (𝔼 u : (∀ i, Fin (N i)), score (fun i => ((u i).val : ℤ))) ≤
            (𝔼 u ∈ A.integerPoints, score u) ∧
          ∃ T : (OrdinaryPolynomialPhase.nilmanifold r).Niltest
              (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1),
            T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget r) ∧
            (9 / 10 : ℝ) ≤ ‖𝔼 u ∈ A.integerPoints,
              majorPhasePlateauSignal J (r + 1) poly
                (fun i => (c (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
                (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
                  (lowTaggedVectorRestrict J (r + 1)
                    (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
                      fast.toSubmodule (r + 1)
                      (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
                (jointIntegerPhysicalSite (finiteSplitPoint keep u fixed) (origin, v)) *
                star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q u))‖ := by
  let N := fun i : {i : LayerSamplerVariables G I n B // keep i} =>
    Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val
  obtain ⟨reset, hreset, hresetbound, hlreset, hlocal⟩ :=
    (Classical.choose_spec (exists_actual_path_buffered_localMajor_niltest.{0, 0, 0, 0} s a)).2
      (τ := {i : LayerSamplerVariables G I n B // keep i}) (κ := κ)
      F b ω hF H l p hH hl hp hι hτ hκ hHp hlp hbracket N hN
  refine ⟨reset, hreset, hresetbound, hlreset, ?_⟩
  intro r _ _ _ _ hr fast vg hspan hvg η eQ j c origin v sample read hread fixed hfixed
    hσ1 Cgeo hCgeo hchart hsmall hpoly K Bstage pK M LongSide blocks hcertificate
    hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
  dsimp only
  intro g E R hinvariant El Pl Rl hfactor hPl hEl hE hRl hR Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal
  have hβ := allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm c origin v sample keep fixed
  have hrange := hread.integerFrozenFullChart_certified_top_range B Utag btag hbtag otag S hRad hσ
    poly hm hσ1 c origin v sample read K hcertificate hretained hpK hBpK hJ
    Cgeo hCgeo hchart hM hcap keep hLong hlong hthreshold fixed
  have hbuffer := hread.integerFrozenFullChart_low_residual B Utag btag hbtag otag S hRad hσ poly hm
    hσ1 Cgeo hCgeo hchart hsmall hpoly c origin v sample read keep fixed hfixed (r + 1)
  obtain ⟨q, hq, hqbound, A, hAdense, hscore, T, hTnorm, hTcomplexity, hcorr⟩ :=
    hlocal hr fast vg hspan hvg J eQ j poly
      (fun i => (c (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
      (allocatedFrozenIntegerFullChart B Utag btag otag poly hm c origin v sample keep fixed)
      hβ K hrange g E R hinvariant El Pl Rl hfactor hPl hEl hE hRl hR
      Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal hbuffer
  refine ⟨q, hq, hqbound, A, hAdense, hscore, T, hTnorm, hTcomplexity, ?_⟩
  simpa only [allocatedFrozenIntegerFullChart_spatial] using hcorr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped TensorProduct BigOperators Classical
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

variable {mTag : ℕ} {G X : Type} [Fintype G] [Fintype X] {I Deck J : Fin mTag → Type}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin mTag → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
variable (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (Utag j)))
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
variable {Rad σ : Fin mTag → ℝ} (S : LayerSamplerScale (G := G) B Utag btag Rad σ)
variable (hRad : ∀ j, 0 < Rad j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)

theorem exists_allocated_controlled_frozen_current_grade_local_niltest (s a : ℕ)
    (keep : LayerSamplerVariables G I n B → Prop)
    {ι κ L : Type} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H lLocal : ℕ) (p : ℝ) (hH : 1 ≤ H) (hlLocal : 0 < lLocal) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hτ : (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    (E R : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Nambient : X → ℕ) (hNambient : ∀ i, 0 < Nambient i) {budget : ℝ}
    (hcontrol : FullChartControlledFactors F b ω hF J poly Nambient E R budget)
    (hcommon : Real.exp budget * (lLocal : ℝ) ≤ Real.exp p)
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((mTag + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ mTag) ^ s)
        ≤ Real.exp ((p + 2) ^ a))
    (hN : ∀ i : {i : LayerSamplerVariables G I n B // keep i},
      Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ≤
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val : ℕ) : ℝ)) :
    ∃ qCurrent : ℕ, 0 < qCurrent ∧ (qCurrent : ℝ) ≤ Real.exp budget ∧
    ∃ reset : ℕ, 0 < reset ∧
      (reset : ℝ) ≤ Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ∧ qCurrent * lLocal ∣ reset ∧
      ∀ {r : ℕ}
        [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)], r ≤ s →
      ∀ (fast : LieSubalgebra ℚ F.AssociatedGraded)
        (vg : κ → F.PolynomialSymbol (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      Submodule.span ℚ (Set.range vg) =
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast).toSubmodule →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)).repr (vg i) z) H) →
      ∀ {η : Type} (eQ : Basis η ℚ (F.AssociatedGraded ⧸ fast.toSubmodule)) (j : η)
        (c : ∀ j, Utag j) (origin : X → ℤ)
        (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
        (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ),
      AllocatedCenteredFramedRecoveredSampleAt B Utag btag hbtag otag S hRad hσ poly hm c origin v sample read →
      ∀ {τ ξ : ℝ}, 0 < τ → τ ≤ 1 → ξ ≤ 1 →
      v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths
          (allocatedPhysicalRootBudget B Utag btag S (fun _ => 0)) τ ξ Nambient) 1 →
      ∀ (fixed : {i : LayerSamplerVariables G I n B // ¬keep i} → ℤ),
      (∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val) →
      (∀ j, σ j ≤ 1) →
      ∀ (Cgeo : Fin mTag → ℝ), (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (Utag j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8) →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      ∀ (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (Bstage pK M LongSide : ℝ) (blocks : ℕ),
      RationalTaggedConstraintCertificate J Set.univ K Bstage blocks →
      (∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      0 ≤ pK → Bstage ≤ pK → (∀ j, (Fintype.card (J j) : ℝ) ≤ pK) →
      0 ≤ M → (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ M) →
      1 ≤ LongSide →
      (∀ i, keep i → LongSide ≤ layerSamplerBox B Utag btag S i) →
      Real.exp ((pK + 2) ^ 9) ^ 2 * M < LongSide →
      let β := allocatedFrozenIntegerFullChart B Utag btag otag poly hm c origin v sample keep fixed
      let N := fun i : {i : LayerSamplerVariables G I n B // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val
      ∀ (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group),
      (∀ t ∈ K, ∀ d < r + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) d t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord ∈
            realificationLieSubalgebra fast) →
      ∀ (El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
          (integerSampledRealChart β)
          (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm c origin v sample keep fixed) g) →
      Pl.coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast) →
      F.SymbolSlowBound b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => (N i : ℝ)) (Real.exp ((p + 2) ^ a)) El →
      F.SymbolRationalGrid b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) lLocal Rl →
      ∀ (Hθ : ℕ) (pLocal : ℝ),
      (∀ i, RationalHeightLE (((eQ.coord j).comp fast.toSubmodule.mkQ)
        (F.associatedGradedBasis b ω hF i)) Hθ) →
      1 ≤ pLocal → (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ pLocal →
      (Fintype.card ι : ℝ) * Hθ *
        Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
          allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal →
      ((Hθ ^ Fintype.card ι * reset : ℕ) : ℝ) ≤ Real.exp pLocal →
      ∀ score : ({i : LayerSamplerVariables G I n B // keep i} → ℤ) → ℝ,
      (∀ i, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (N i : ℝ)) →
      ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * reset ∧
        ∃ A : ResidueBoxSlice N q,
          IsDenseCommonStrideBox N ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) A.integerPoints ∧
          (𝔼 u : (∀ i, Fin (N i)), score (fun i => ((u i).val : ℤ))) ≤
            (𝔼 u ∈ A.integerPoints, score u) ∧
          ∃ T : (OrdinaryPolynomialPhase.nilmanifold r).Niltest
              (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1),
            T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget r) ∧
            (9 / 10 : ℝ) ≤ ‖𝔼 u ∈ A.integerPoints,
              majorPhasePlateauSignal J (r + 1) poly
                (fun i => (c (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
                (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
                  (lowTaggedVectorRestrict J (r + 1)
                    (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
                      fast.toSubmodule (r + 1)
                      (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
                (jointIntegerPhysicalSite (finiteSplitPoint keep u fixed) (origin, v)) *
                star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q u))‖ := by
  obtain ⟨qCurrent, hqCurrent, hqCurrentBound, hpulls⟩ :=
    hcontrol.exists_allocated_frozen_pullbacks B Utag btag hbtag otag S hRad hσ poly hm
      F b ω hF E R Nambient hNambient hallowance
  have hl : 0 < qCurrent * lLocal := Nat.mul_pos hqCurrent hlLocal
  have hlp : ((qCurrent * lLocal : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hqCurrentBound (Nat.cast_nonneg lLocal)).trans hcommon
  obtain ⟨reset, hreset, hresetbound, hlreset, hlocal⟩ :=
    exists_allocated_frozen_current_grade_local_niltest B Utag btag hbtag otag S hRad hσ poly hm
      s a keep F b ω hF H (qCurrent * lLocal) p hH hl hp hι hτ hκ hHp hlp hbracket hN
  refine ⟨qCurrent, hqCurrent, hqCurrentBound, reset, hreset, hresetbound, hlreset, ?_⟩
  intro r _ _ _ _ hr fast vg hspan hvg η eQ j c origin v sample read hread
    τ ξ hτpos hτone hξ hv fixed hfixed hσ1 Cgeo hCgeo hchart hsmall hpoly
    K Bstage pK M LongSide blocks hcertificate hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
  dsimp only
  intro g hinvariant El Pl Rl hfactor hPl hEl hRl Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal
  have hsmallOne : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 :=
    fun j => (hsmall j).trans (by norm_num)
  have hcurrent := hpulls c origin v sample read hread keep fixed
  have hpullR := hcurrent.1 (qCurrent * lLocal) (dvd_mul_right qCurrent lLocal)
  have hpullE := hcurrent.2 hτpos hτone hξ hv hσ1 hpoly Cgeo hCgeo hchart hsmallOne
  have hlocalR := F.symbolRationalGrid_mono b ω hF
    (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
    hlLocal (dvd_mul_left lLocal qCurrent) Rl hRl
  exact hlocal hr fast vg hspan hvg eQ j c origin v sample read hread fixed hfixed
    hσ1 Cgeo hCgeo hchart hsmall hpoly K Bstage pK M LongSide blocks hcertificate
    hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
    g E R hinvariant El Pl Rl hfactor hPl hEl hpullE hlocalR hpullR
    Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped TensorProduct BigOperators Classical
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

variable {mTag : ℕ} {G X : Type} [Fintype G] [Fintype X] {I Deck J : Fin mTag → Type}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin mTag → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
variable (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (Utag j)))
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
variable {Rad σ : Fin mTag → ℝ} (S : LayerSamplerScale (G := G) B Utag btag Rad σ)
variable (hRad : ∀ j, 0 < Rad j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)

theorem exists_allocated_common_frozen_current_grade_local_niltest (s a : ℕ)
    (keep : LayerSamplerVariables G I n B → Prop)
    {ι κ L : Type} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H lLocal : ℕ) (p : ℝ) (hH : 1 ≤ H) (hlLocal : 0 < lLocal) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hτ : (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    (E R : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Nambient : X → ℕ) (hNambient : ∀ i, 0 < Nambient i) {budget : ℝ}
    (hcontrol : FullChartControlledFactors F b ω hF J poly Nambient E R budget)
    (hcommon : Real.exp budget * (lLocal : ℝ) ≤ Real.exp p)
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((mTag + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ mTag) ^ s)
        ≤ Real.exp ((p + 2) ^ a))
    (hN : ∀ i : {i : LayerSamplerVariables G I n B // keep i},
      Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ≤
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val : ℕ) : ℝ)) :
    ∃ qCurrent : ℕ, 0 < qCurrent ∧ (qCurrent : ℝ) ≤ Real.exp budget ∧
    ∃ reset : ℕ, 0 < reset ∧
      (reset : ℝ) ≤ Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ∧ qCurrent * lLocal ∣ reset ∧
      ∀ {r : ℕ}
        [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)], r ≤ s →
      ∀ (fast : LieSubalgebra ℚ F.AssociatedGraded)
        (vg : κ → F.PolynomialSymbol (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      Submodule.span ℚ (Set.range vg) =
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast).toSubmodule →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)).repr (vg i) z) H) →
      ∀ {η : Type} (eQ : Basis η ℚ (F.AssociatedGraded ⧸ fast.toSubmodule)) (j : η)
        (c : ∀ j, Utag j) (origin : X → ℤ)
        (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
        (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ),
      AllocatedCenteredFramedRecoveredSampleAt B Utag btag hbtag otag S hRad hσ poly hm c origin v sample read →
      ∀ {τ ξ : ℝ}, 0 < τ → τ ≤ 1 → ξ ≤ 1 →
      v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths
          (allocatedPhysicalRootBudget B Utag btag S (fun _ => 0)) τ ξ Nambient) 1 →
      ∀ (fixed : {i : LayerSamplerVariables G I n B // ¬keep i} → ℤ),
      (∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val) →
      (∀ j, σ j ≤ 1) →
      ∀ (Cgeo : Fin mTag → ℝ), (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (Utag j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8) →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      ∀ (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (Bstage pK M LongSide : ℝ) (blocks : ℕ),
      RationalTaggedConstraintCertificate J Set.univ K Bstage blocks →
      (∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      0 ≤ pK → Bstage ≤ pK → (∀ j, (Fintype.card (J j) : ℝ) ≤ pK) →
      0 ≤ M → (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ M) →
      1 ≤ LongSide →
      (∀ i, keep i → LongSide ≤ layerSamplerBox B Utag btag S i) →
      Real.exp ((pK + 2) ^ 9) ^ 2 * M < LongSide →
      let N := fun i : {i : LayerSamplerVariables G I n B // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val
      ∀ (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group),
      (∀ t ∈ K, ∀ d < r + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) d t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord ∈
            realificationLieSubalgebra fast) →
      F.HasCommonRefilteredOrbitFactors b ω hF
        (layerSamplerBox B Utag btag S) ((p + 2) ^ a) lLocal fast
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : LayerSamplerVariables G I n B => 1)
          (integerSampledRealChart
            (allocatedRecoveredIntegerFullChart B Utag btag otag poly hm c origin v sample))
          (allocatedRecoveredIntegerFullChart_support B Utag btag otag poly hm c origin v sample) g) →
      ∀ (Hθ : ℕ) (pLocal : ℝ),
      (∀ i, RationalHeightLE (((eQ.coord j).comp fast.toSubmodule.mkQ)
        (F.associatedGradedBasis b ω hF i)) Hθ) →
      1 ≤ pLocal → (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ pLocal →
      (Fintype.card ι : ℝ) * Hθ *
        Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
          allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal →
      ((Hθ ^ Fintype.card ι * reset : ℕ) : ℝ) ≤ Real.exp pLocal →
      ∀ score : ({i : LayerSamplerVariables G I n B // keep i} → ℤ) → ℝ,
      (∀ i, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (N i : ℝ)) →
      ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * reset ∧
        ∃ A : ResidueBoxSlice N q,
          IsDenseCommonStrideBox N ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) A.integerPoints ∧
          (𝔼 u : (∀ i, Fin (N i)), score (fun i => ((u i).val : ℤ))) ≤
            (𝔼 u ∈ A.integerPoints, score u) ∧
          ∃ T : (OrdinaryPolynomialPhase.nilmanifold r).Niltest
              (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1),
            T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget r) ∧
            (9 / 10 : ℝ) ≤ ‖𝔼 u ∈ A.integerPoints,
              majorPhasePlateauSignal J (r + 1) poly
                (fun i => (c (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
                (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
                  (lowTaggedVectorRestrict J (r + 1)
                    (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
                      fast.toSubmodule (r + 1)
                      (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
                (jointIntegerPhysicalSite (finiteSplitPoint keep u fixed) (origin, v)) *
                star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q u))‖ := by
  obtain ⟨qCurrent, hqCurrent, hqCurrentBound, reset, hreset, hresetbound, hlreset, hlocal⟩ :=
    exists_allocated_controlled_frozen_current_grade_local_niltest B Utag btag hbtag otag S hRad hσ poly hm
      s a keep F b ω hF H lLocal p hH hlLocal hp hι hτ hκ hHp hbracket
      E R Nambient hNambient hcontrol hcommon hallowance hN
  refine ⟨qCurrent, hqCurrent, hqCurrentBound, reset, hreset, hresetbound, hlreset, ?_⟩
  intro r _ _ _ _ hr fast vg hspan hvg η eQ j c origin v sample read hread
    τ ξ hτpos hτone hξ hv fixed hfixed hσ1 Cgeo hCgeo hchart hsmall hpoly
    K Bstage pK M LongSide blocks hcertificate hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
  dsimp only
  intro g hinvariant hnative Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal
  obtain ⟨El, Pl, Rl, hfactor, hPl, hEl, hRl⟩ :=
    hnative.allocatedFrozenSymbolFactors F b ω hF B Utag btag otag S poly hm
      c origin v sample keep fixed ((p + 2) ^ a) lLocal fast g
  exact hlocal hr fast vg hspan hvg eQ j c origin v sample read hread hτpos hτone hξ hv
    fixed hfixed hσ1 Cgeo hCgeo hchart hsmall hpoly K Bstage pK M LongSide blocks hcertificate
    hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
    g hinvariant El Pl Rl hfactor hPl hEl hRl
    Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3
open Module VectorPolynomial Submodule BooleanCubeKernel RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag R σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U btag S hb o hR hσ N poly hm τ ξ stride cells center)

namespace NilpotentLieFiltration

theorem exists_allocated_full_chart_major_correlation_witness_of_frozen_local_niltests
    {k t : ℕ} {L ι η : Type} [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pSlice pTest pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (good : η → Finset A.Path)
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost Bshort : ℝ) (hcost : 0 ≤ cost)
    (hBshort : 1 ≤ Bshort) (hshort : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Bshort)
    (hξ : ξ ≤ 1)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * A.law.mass (good j))
    (hdirect : A.NativeDetection t pSlice pTest pNative α)
    (hslice : max cost (Real.log Bshort) ≤ pSlice)
    (htest : OrdinaryPolynomialPhase.budget t ≤ pTest)
    (strideBound : η → A.Path → ℕ)
    (score : η → A.Path → ({i : LayerSamplerVariables G I n B // keep i} → ℤ) → ℝ)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep i} → ℤ,
        (∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val) ∧
      ∃ q : ℕ, 0 < q ∧ q ≤ strideBound j z ∧
      ∃ slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q,
        IsDenseCommonStrideBox (fun i : {i // keep i} => A.sides i.val) cost slice.integerPoints ∧
        (𝔼 x : (∀ i : {i // keep i}, Fin (A.sides i.val)),
          score j z (fun i => ((x i).val : ℤ))) ≤
          (𝔼 x ∈ slice.integerPoints, score j z x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold t).Niltest (fun _ : {i // keep i} => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget t) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (jointIntegerPhysicalSite (finiteSplitPoint keep x fixed) (z.1.val, z.2.val)) *
              star (T.eval (commonStrideIndex (fun i => (slice.start i : ℤ)) q x))‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  apply exists_allocated_full_chart_major_correlation_witness_of_frozen_local_tests
    A F b ω hF fast basis Z left right htk hpoly c pSlice pTest pNative pMajor Rrank C
    hpNative hη hNativeMajor hproduct hdim hN hRrank hrank good keep cost Bshort
    hcost hBshort hshort hξ α hmass hdirect hslice htest
  intro j z hz
  obtain ⟨fixed, hfixed, q, hq, _, slice, hdense, _, T, hnorm, hcomplex, hcorr⟩ := hlocal j z hz
  let packet : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t)
      (fun i : {i // keep i} => A.sides i.val) cost (OrdinaryPolynomialPhase.budget t) :=
    { stride := q
      stride_pos := hq
      slice := slice
      dense := hdense
      test := T
      norm := by rw [hnorm]; norm_num
      complexity := hcomplex }
  exact ⟨fixed, hfixed, packet, hcorr⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped TensorProduct BigOperators Classical
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

variable {mTag : ℕ} {G X : Type} [Fintype G] [Fintype X] {I Deck J : Fin mTag → Type}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin mTag → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
variable (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (Utag j)))
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
variable {Rad σ : Fin mTag → ℝ} (S : LayerSamplerScale (G := G) B Utag btag Rad σ)
variable (hRad : ∀ j, 0 < Rad j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)

theorem exists_allocated_kept_common_current_grade_local_niltest (s a : ℕ)
    (keep : LayerSamplerVariables G I n B → Prop)
    {ι κ L : Type} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H lLocal : ℕ) (p : ℝ) (hH : 1 ≤ H) (hlLocal : 0 < lLocal) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hτ : (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    (E R : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Nambient : X → ℕ) (hNambient : ∀ i, 0 < Nambient i) {budget : ℝ}
    (hcontrol : FullChartControlledFactors F b ω hF J poly Nambient E R budget)
    (hcommon : Real.exp budget * (lLocal : ℝ) ≤ Real.exp p)
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((mTag + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ mTag) ^ s)
        ≤ Real.exp ((p + 2) ^ a))
    (hN : ∀ i : {i : LayerSamplerVariables G I n B // keep i},
      Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ≤
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val : ℕ) : ℝ)) :
    ∃ qCurrent : ℕ, 0 < qCurrent ∧ (qCurrent : ℝ) ≤ Real.exp budget ∧
    ∃ reset : ℕ, 0 < reset ∧
      (reset : ℝ) ≤ Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ∧ qCurrent * lLocal ∣ reset ∧
      ∀ {r : ℕ}
        [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)], r ≤ s →
      ∀ (fast : LieSubalgebra ℚ F.AssociatedGraded)
        (vg : κ → F.PolynomialSymbol (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      Submodule.span ℚ (Set.range vg) =
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast).toSubmodule →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)).repr (vg i) z) H) →
      ∀ {η : Type} (eQ : Basis η ℚ (F.AssociatedGraded ⧸ fast.toSubmodule)) (j : η)
        (c : ∀ j, Utag j) (origin : X → ℤ)
        (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
        (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ),
      AllocatedCenteredFramedRecoveredSampleAt B Utag btag hbtag otag S hRad hσ poly hm c origin v sample read →
      ∀ {τ ξ : ℝ}, 0 < τ → τ ≤ 1 → ξ ≤ 1 →
      v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths
          (allocatedPhysicalRootBudget B Utag btag S (fun _ => 0)) τ ξ Nambient) 1 →
      ∀ (fixed : {i : LayerSamplerVariables G I n B // ¬keep i} → ℤ),
      (∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val) →
      (∀ j, σ j ≤ 1) →
      ∀ (Cgeo : Fin mTag → ℝ), (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (Utag j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8) →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      ∀ (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (Bstage pK M LongSide : ℝ) (blocks : ℕ),
      RationalTaggedConstraintCertificate J Set.univ K Bstage blocks →
      (∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      0 ≤ pK → Bstage ≤ pK → (∀ j, (Fintype.card (J j) : ℝ) ≤ pK) →
      0 ≤ M → (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ M) →
      1 ≤ LongSide →
      (∀ i, keep i → LongSide ≤ layerSamplerBox B Utag btag S i) →
      Real.exp ((pK + 2) ^ 9) ^ 2 * M < LongSide →
      let N := fun i : {i : LayerSamplerVariables G I n B // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val
      ∀ (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group),
      (∀ t ∈ K, ∀ d < r + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) d t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord ∈
            realificationLieSubalgebra fast) →
      F.HasCommonRefilteredOrbitFactors b ω hF
        (fun i : {i : LayerSamplerVariables G I n B // keep i} => (N i : ℝ))
        ((p + 2) ^ a) lLocal fast
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
          (integerSampledRealChart
            (allocatedFrozenIntegerFullChart B Utag btag otag poly hm c origin v sample keep fixed))
          (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm c origin v sample keep fixed) g) →
      ∀ (Hθ : ℕ) (pLocal : ℝ),
      (∀ i, RationalHeightLE (((eQ.coord j).comp fast.toSubmodule.mkQ)
        (F.associatedGradedBasis b ω hF i)) Hθ) →
      1 ≤ pLocal → (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ pLocal →
      (Fintype.card ι : ℝ) * Hθ *
        Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
          allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal →
      ((Hθ ^ Fintype.card ι * reset : ℕ) : ℝ) ≤ Real.exp pLocal →
      ∀ score : ({i : LayerSamplerVariables G I n B // keep i} → ℤ) → ℝ,
      (∀ i, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (N i : ℝ)) →
      ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * reset ∧
        ∃ A : ResidueBoxSlice N q,
          IsDenseCommonStrideBox N ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) A.integerPoints ∧
          (𝔼 u : (∀ i, Fin (N i)), score (fun i => ((u i).val : ℤ))) ≤
            (𝔼 u ∈ A.integerPoints, score u) ∧
          ∃ T : (OrdinaryPolynomialPhase.nilmanifold r).Niltest
              (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1),
            T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget r) ∧
            (9 / 10 : ℝ) ≤ ‖𝔼 u ∈ A.integerPoints,
              majorPhasePlateauSignal J (r + 1) poly
                (fun i => (c (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
                (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
                  (lowTaggedVectorRestrict J (r + 1)
                    (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
                      fast.toSubmodule (r + 1)
                      (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
                (jointIntegerPhysicalSite (finiteSplitPoint keep u fixed) (origin, v)) *
                star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q u))‖ := by
  obtain ⟨qCurrent, hqCurrent, hqCurrentBound, reset, hreset, hresetbound, hlreset, hlocal⟩ :=
    exists_allocated_controlled_frozen_current_grade_local_niltest B Utag btag hbtag otag S hRad hσ poly hm
      s a keep F b ω hF H lLocal p hH hlLocal hp hι hτ hκ hHp hbracket
      E R Nambient hNambient hcontrol hcommon hallowance hN
  refine ⟨qCurrent, hqCurrent, hqCurrentBound, reset, hreset, hresetbound, hlreset, ?_⟩
  intro r _ _ _ _ hr fast vg hspan hvg η eQ j c origin v sample read hread
    τ ξ hτpos hτone hξ hv fixed hfixed hσ1 Cgeo hCgeo hchart hsmall hpoly
    K Bstage pK M LongSide blocks hcertificate hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
  dsimp only
  intro g hinvariant hnative Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal
  obtain ⟨El, Pl, Rl, hfactor, hPl, hEl, hRl⟩ :=
    hnative.symbolFactors F b ω hF _ ((p + 2) ^ a) lLocal fast _
  exact hlocal hr fast vg hspan hvg eQ j c origin v sample read hread hτpos hτone hξ hv
    fixed hfixed hσ1 Cgeo hCgeo hchart hsmall hpoly K Bstage pK M LongSide blocks hcertificate
    hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
    g hinvariant El Pl Rl hfactor hPl hEl hRl
    Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal

end Erdos3.NilpotentLieFiltration

end

end OAI
