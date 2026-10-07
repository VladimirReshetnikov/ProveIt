/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.FullChartPolynomialLiftControl

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedPolynomialProjection (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  F.realGradedSymbolPolynomial b ω hF w (F.realSymbolOfGradedPolynomial b ω hF w P)

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolOfGradedPolynomial realSymbolHomogeneousPullback gradedPolynomialProjection

theorem coefficients_gradedPolynomialProjection (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) (α : σ →₀ ℕ) :
    coefficients (F.gradedPolynomialProjection b ω hF w P) α =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω
        (Finsupp.weight w α) (coefficients P α) := by
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [basisGradeProjection_repr, gradedPolynomialProjection]
  by_cases hi : Finsupp.weight w α = ω i
  · rw [ite_eq_left hi.symm,
      F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(α, i), hi⟩,
      F.realSymbolOfGradedPolynomial_coordinate]
  · rw [ite_eq_right (Ne.symm hi),
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ α i hi]

theorem gradedPolynomialProjection_mem (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    F.gradedPolynomialProjection b ω hF w P ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w := by
  rw [gradedPolynomialProjection]
  exact F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule b ω hF w _

theorem gradedPolynomialProjection_eq_self (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : P ∈ gradedPolynomialSubmodule
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w) :
    F.gradedPolynomialProjection b ω hF w P = P := by
  rw [gradedPolynomialProjection]
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF w P hP

theorem gradedPolynomialProjection_degreeLE (w u : σ → ℕ) (d : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : DegreeLE u d P) :
    DegreeLE u d (F.gradedPolynomialProjection b ω hF w P) := by
  intro α hα
  rw [F.coefficients_gradedPolynomialProjection, hP α hα, map_zero]

theorem gradedPolynomialProjection_coefficientBound (w : σ → ℕ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M P) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
      (F.gradedPolynomialProjection b ω hF w P) := by
  intro α i
  rw [F.coefficients_gradedPolynomialProjection, basisGradeProjection_repr]
  split_ifs
  · exact hP α i
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realSymbolOfGradedPolynomial_homogeneousChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    F.realSymbolOfGradedPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolHomogeneousPullback b ω hF w v β
        (F.realSymbolOfGradedPolynomial b ω hF w p) := by
  classical
  apply ((F.polynomialSymbolBasis b ω hF v).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfGradedPolynomial_coordinate, realSymbolHomogeneousPullback,
    F.realSymbolOfGradedPolynomial_coordinate]
  rw [coefficients_realChartSubstitute, coefficients_realChartSubstitute]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr_of_eq_on_inter
  · intro γ hγ hγ'
    have hz : coefficients (F.realGradedSymbolPolynomial b ω hF w
        (F.realSymbolOfGradedPolynomial b ω hF w p)) γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · have he := F.realGradedSymbolPolynomial_coordinate b ω hF w
        (F.realSymbolOfGradedPolynomial b ω hF w p) ⟨(γ, z.val.2), h⟩
      rw [hz, map_zero, Finsupp.zero_apply, F.realSymbolOfGradedPolynomial_coordinate] at he
      rw [← he, mul_zero]
    · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _
        (fun he => h (he.symm.trans z.property)), zero_mul]
  · intro γ hγ hγ'
    have hz : coefficients p γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfGradedPolynomial_coordinate, hz, map_zero, Finsupp.zero_apply, mul_zero]
    · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ γ z.val.2 h, mul_zero]
  · intro γ hγ hγ'
    have hz := z.property
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfGradedPolynomial_coordinate]
    · have ha : Finsupp.weight v z.val.1 ≠ Finsupp.weight w γ :=
        fun he => h (he.symm.trans hz)
      rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _ ha]
      simp only [zero_mul]

theorem gradedPolynomialProjection_realChartSubstitute
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    F.gradedPolynomialProjection b ω hF v (realChartSubstitute β P) =
      realChartSubstitute β (F.gradedPolynomialProjection b ω hF w P) := by
  rw [gradedPolynomialProjection, gradedPolynomialProjection,
    F.realSymbolOfGradedPolynomial_homogeneousChart b ω hF w v β hβ]
  exact F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ _

theorem FullChartControlledFactors.exists_graded_degree_bounded_chart
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∃ Echart : PolynomialGroup (X ⊕ (Σ j, J j))
          F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
        F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left =
          realPolynomialChartSubstitution
            F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
            (normalizedRealPolynomialChart (fun i => (N i : ℝ))
              (fullTaggedMajorTopCoordinates J poly)) Echart ∧
        CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
          (Real.exp budget) Echart.coord ∧
        Echart.coord ∈ gradedPolynomialSubmodule
          ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω
          (fullTaggedVariableWeight (X := X) J) ∧
        DegreeLE (fullTaggedVariableWeight (X := X) J) s Echart.coord ∧
        DegreeLE (fun _ => 1) s Echart.coord ∧
        CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
          (F.realGradedSymbolPolynomialHom b ω hF
            (fullTaggedVariableWeight (X := X) J) right).coord := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_degree_bounded_chart F b ω hF J poly N left right h
  let w := fullTaggedVariableWeight (X := X) J
  let E' : PolynomialGroup (X ⊕ (Σ j, J j))
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
    ⟨F.gradedPolynomialProjection b ω hF w E.coord⟩
  refine ⟨q, hq, hqB, E', ?_, ?_, F.gradedPolynomialProjection_mem b ω hF w E.coord,
    F.gradedPolynomialProjection_degreeLE b ω hF w w s E.coord hweighted,
    F.gradedPolynomialProjection_degreeLE b ω hF w (fun _ => 1) s E.coord hdegree, hgrid⟩
  · apply NilpotentLieBCHGroup.ext
    have he := congrArg NilpotentLieBCHGroup.coord hchart
    rw [realPolynomialChartSubstitution_coord] at he
    change F.realGradedSymbolPolynomial b ω hF w left.coord =
      realChartSubstitute
        (normalizedRealPolynomialChart (fun i => (N i : ℝ))
          (fullTaggedMajorTopCoordinates J poly))
        (F.gradedPolynomialProjection b ω hF w E.coord)
    have hgraded := F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule
      b ω hF w left.coord
    rw [← F.gradedPolynomialProjection_realChartSubstitute b ω hF w w _
      (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ))) E.coord,
      ← he]
    exact (F.gradedPolynomialProjection_eq_self b ω hF w _ hgraded).symm
  · exact F.gradedPolynomialProjection_coefficientBound b ω hF w _
      (fun _ => zero_lt_one) (Real.exp_pos budget).le E.coord hbound

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ τ : Type*} {ι L : Type} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] realChartSubstitute realSymbolOfGradedPolynomial
  realGradedSymbolPolynomial realSymbolHomogeneousPullback

omit [Fintype σ] in

theorem exists_inhomogeneous_chart_lift_algebraic
    (w : σ → ℕ) (v : τ → ℕ) (E : F.RealPolynomialSymbolGroup w)
    (f : σ → MvPolynomial σ ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hgraded : P ∈ gradedPolynomialSubmodule
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w)
    (hchart : (F.realGradedSymbolPolynomialHom b ω hF w E).coord =
      realChartSubstitute f P)
    (β δ : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v (w i))
    (htop : ∀ i, MvPolynomial.weightedHomogeneousComponent v (w i) (δ i) =
      MvPolynomial.aeval β (f i)) :
    ∃ e : (F.realification.adaptedPolynomialFiltration v).Group,
      e.coord.val = realChartSubstitute δ (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ∧
      F.realPolynomialSymbolHom b ω hF v e =
        F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ E := by
  let Y : F.RealPolynomialSymbolGroup w := ⟨F.realSymbolOfGradedPolynomial b ω hF w P⟩
  have hY : F.realGradedSymbolPolynomial b ω hF w Y.coord = P :=
    F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF w P hgraded
  let S := (F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ
  have hlog : (F.realPolynomialSymbolLift b ω hF w Y).coord.val =
      VectorPolynomial.map (S.restrictScalars ℚ) P := by
    rw [F.realPolynomialSymbolLift_log, F.realSymbolRepresentative_eq_map, hY]
  let e := F.weightedAdaptedRealChartHom w v δ hδ
    (F.realPolynomialSymbolLift b ω hF w Y)
  have he : e.coord.val = realChartSubstitute δ
      (VectorPolynomial.map (S.restrictScalars ℚ) P) := by
    change realChartSubstitute δ (F.realPolynomialSymbolLift b ω hF w Y).coord.val = _
    rw [hlog]
  refine ⟨e, he, ?_⟩
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart,
      F.realPolynomialSymbolHom_lift]
  apply F.realGradedSymbolPolynomialHom_injective b ω hF v
  apply NilpotentLieBCHGroup.ext
  change F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v _ Y.coord) =
      F.realGradedSymbolPolynomial b ω hF v
        (F.realSymbolHomogeneousPullback b ω hF w v β E.coord)
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v _
      (fun _ => MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _),
      F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ, hY]
  change realChartSubstitute _ P =
      realChartSubstitute β (F.realGradedSymbolPolynomialHom b ω hF w E).coord
  rw [hchart, realChartSubstitute_comp]
  exact congrArg (fun z => realChartSubstitute z P) (funext htop)

theorem polynomialSlowBound_inhomogeneous_chart_lift
    {υ : Type*} (v : τ → ℕ) (u : υ → ℕ)
    (e : (F.realification.adaptedPolynomialFiltration v).Group)
    (δ : σ → MvPolynomial τ ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (he : e.coord.val = realChartSubstitute δ (VectorPolynomial.map
      (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P))
    (γ : τ → MvPolynomial υ ℝ) (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
    (T : υ → ℝ) (hT : ∀ i, 0 < T i) {A B : ℝ} {d : ℕ}
    (hbound : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ)
      (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) d P)
    (hmass : ∀ i, realPolynomialMass
      (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ B) :
    F.PolynomialSlowBound b u T
      (((Fintype.card σ : ℝ) + 1) ^ d * A * B ^ d)
      (F.weightedAdaptedRealChartHom v u γ hγ e) := by
  change CoefficientBound (b.baseChange ℝ) T _ (realChartSubstitute γ e.coord.val)
  rw [he, realChartSubstitute_comp]
  exact CoefficientBound.realChartSubstitute_sharp (b.baseChange ℝ) T hT _
    ((F.coefficientBound_gradedBasisSplitting b ω hF _ _ P).mpr hbound)
    hA hB (hdegree.map _) hmass

theorem exists_inhomogeneous_chart_lift
    (w : σ → ℕ) (v : τ → ℕ) (E : F.RealPolynomialSymbolGroup w)
    (f : σ → MvPolynomial σ ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hgraded : P ∈ gradedPolynomialSubmodule
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w)
    (hchart : (F.realGradedSymbolPolynomialHom b ω hF w E).coord =
      realChartSubstitute f P)
    (β δ : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v (w i))
    (htop : ∀ i, MvPolynomial.weightedHomogeneousComponent v (w i) (δ i) =
      MvPolynomial.aeval β (f i))
    (T : τ → ℝ) (hT : ∀ i, 0 < T i) {A B : ℝ} {d : ℕ}
    (hbound : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ)
      (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) d P)
    (hmass : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (δ i)) ≤ B) :
    ∃ e : (F.realification.adaptedPolynomialFiltration v).Group,
      e.coord.val = realChartSubstitute δ (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ∧
      F.realPolynomialSymbolHom b ω hF v e =
        F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ E ∧
      F.PolynomialSlowBound b v T
        (((Fintype.card σ : ℝ) + 1) ^ d * A * B ^ d) e := by
  obtain ⟨e, he, hsymbol⟩ := F.exists_inhomogeneous_chart_lift_algebraic b ω hF
    w v E f P hgraded hchart β δ hβ hδ htop
  refine ⟨e, he, hsymbol, ?_⟩
  change CoefficientBound (b.baseChange ℝ) T _ e.coord.val
  rw [he]
  exact CoefficientBound.realChartSubstitute_sharp (b.baseChange ℝ) T hT δ
    ((F.coefficientBound_gradedBasisSplitting b ω hF _ _ P).mpr hbound)
    hA hB (hdegree.map _) hmass

theorem FullChartControlledFactors.exists_inhomogeneous_left_lift
    {m : ℕ} {X : Type} [Fintype X]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup
      (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β δ : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v
      (fullTaggedVariableWeight (X := X) J i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v
      (fullTaggedVariableWeight (X := X) J i))
    (htop : ∀ i, MvPolynomial.weightedHomogeneousComponent v
      (fullTaggedVariableWeight (X := X) J i) (δ i) =
      MvPolynomial.aeval β (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i)) :
    ∃ (P : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
      (e : (F.realification.adaptedPolynomialFiltration v).Group),
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ)
        (fun _ => 1) (Real.exp budget) P ∧
      P ∈ gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω
        (fullTaggedVariableWeight (X := X) J) ∧
      DegreeLE (fullTaggedVariableWeight (X := X) J) s P ∧
      DegreeLE (fun _ => 1) s P ∧
      e.coord.val = realChartSubstitute δ (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ∧
      F.realPolynomialSymbolHom b ω hF v e = F.realSymbolHomogeneousPullbackHom b ω hF
        (fullTaggedVariableWeight (X := X) J) v β hβ left := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hgraded, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_graded_degree_bounded_chart
      F b ω hF J poly N left right h
  have hc := congrArg NilpotentLieBCHGroup.coord hchart
  rw [realPolynomialChartSubstitution_coord] at hc
  obtain ⟨e, he, hsymbol⟩ := F.exists_inhomogeneous_chart_lift_algebraic b ω hF
    _ v left _ E.coord hgraded hc β δ hβ hδ htop
  exact ⟨E.coord, e, hbound, hgraded, hweighted, hdegree, he, hsymbol⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
