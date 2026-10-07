/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.VectorRealSubstitutionBound
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartDecompositionSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ τ ι V : Type*}

theorem CoefficientBound.realChartSubstitute_sharp [Fintype σ]
    [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V] [IsScalarTower ℚ ℝ V]
    (b : Basis ι ℝ V) (T : τ → ℝ) (hT : ∀ i, 0 < T i)
    (f : σ → MvPolynomial τ ℝ) {A B : ℝ} {s : ℕ} {P : VectorPolynomial σ ℚ V}
    (hP : CoefficientBound b (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) s P)
    (hf : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (f i)) ≤ B) :
    CoefficientBound b T
      (((Fintype.card σ : ℝ) + 1) ^ s * A * B ^ s)
      (Erdos3.VectorPolynomial.realChartSubstitute f P) := by
  intro α i
  let Q := coordinate (b.coord i).toAddMonoidHom P
  have hQdeg : Q.totalDegree ≤ s :=
    (degreeLE_one_iff_basis_totalDegree b s P).mp hdegree i
  have hQcoeff (β) : |Q.coeff β| ≤ A := by
    change |b.repr (coefficients P β) i| ≤ A
    simpa [monomialScale] using hP β i
  have hcard : (Q.support.card : ℝ) ≤ ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast mvPolynomial_support_card_le_totalDegree Q hQdeg
  have hbound := scaled_substitution_coeff_bound T hT f Q hB hf hQcoeff hQdeg α
  have heq := congrArg (fun q : MvPolynomial τ ℝ => q.coeff α)
    (coordinate_realChartSubstitute (b.coord i) f P)
  rw [coeff_coordinate] at heq
  change (b.coord i)
    (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α) = _ at heq
  change |(b.coord i)
    (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α)| ≤ _
  rw [heq]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (monomialScale_pos T hT α).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hA)
    (pow_nonneg (zero_le_one.trans hB) s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators

variable {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def weightedDegreeTruncate (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) : VectorPolynomial σ R V :=
  ∑ j ∈ Finset.range (d + 1), weightedHomogeneousPart w j p

theorem coefficients_weightedDegreeTruncate (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (weightedDegreeTruncate w d p) α =
      if Finsupp.weight w α ≤ d then coefficients p α else 0 := by
  classical
  simp [weightedDegreeTruncate, coefficients_weightedHomogeneousPart]

theorem degreeLE_weightedDegreeTruncate (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) : DegreeLE w d (weightedDegreeTruncate w d p) := by
  intro α hα
  rw [coefficients_weightedDegreeTruncate, ite_eq_right (not_le_of_gt hα)]

theorem weightedDegreeTruncate_eq_self (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (hp : DegreeLE w d p) :
    weightedDegreeTruncate w d p = p := by
  classical
  apply coefficients.injective
  ext α
  rw [coefficients_weightedDegreeTruncate]
  split_ifs with h
  · rfl
  · exact (hp α (lt_of_not_ge h)).symm

theorem degreeLE_one_weightedDegreeTruncate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE (fun _ => 1) d (weightedDegreeTruncate w d p) := by
  intro α hα
  apply degreeLE_weightedDegreeTruncate w d p α
  have h := exponentSum_le_positive_weight w hw α
  have he : Finsupp.weight (fun _ : σ => 1) α = α.sum (fun _ n => n) := by
    simp [Finsupp.weight_apply]
  rw [he] at hα
  exact hα.trans_le h

section Real
variable {W : Type*} [AddCommGroup W] [Module ℚ W] [Module ℝ W] [IsScalarTower ℚ ℝ W]

theorem realChartSubstitute_weightedDegreeTruncate (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ ℚ W) :
    realChartSubstitute f (weightedDegreeTruncate w d p) =
      weightedDegreeTruncate v d (realChartSubstitute f p) := by
  simp only [weightedDegreeTruncate, map_sum,
    realChartSubstitute_weightedHomogeneousPart w v f hf]
end Real

section Bounds
variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem CoefficientBound.weightedDegreeTruncate (b : Basis ι ℝ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    {p : VectorPolynomial σ ℚ L} (hp : CoefficientBound b T M p)
    (w : σ → ℕ) (d : ℕ) : CoefficientBound b T M (weightedDegreeTruncate w d p) := by
  intro α i
  rw [coefficients_weightedDegreeTruncate]
  split_ifs
  · exact hp α i
  · simp only [map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le
end Bounds

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}

attribute [local irreducible] realChartSubstitute

theorem realPolynomialChartSubstitution_truncate_of_degreeLE
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (w : σ → ℕ)
    (f : σ → MvPolynomial σ ℝ) (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i))
    (d : ℕ) (g E : PolynomialGroup σ hnil)
    (heq : g = realPolynomialChartSubstitution hnil f E) (hg : DegreeLE w d g.coord) :
    g = realPolynomialChartSubstitution hnil f ⟨weightedDegreeTruncate w d E.coord⟩ := by
  apply NilpotentLieBCHGroup.ext
  rw [realPolynomialChartSubstitution_coord]
  have he := congrArg NilpotentLieBCHGroup.coord heq
  rw [realPolynomialChartSubstitution_coord] at he
  have ht := weightedDegreeTruncate_eq_self w d g.coord hg
  have hc := realChartSubstitute_weightedDegreeTruncate w w f hf d E.coord
  exact ht.symm.trans ((congrArg (weightedDegreeTruncate w d) he).trans hc.symm)

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem realGradedSymbolPolynomialHom_degreeLE
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (left : F.RealPolynomialSymbolGroup w) :
    DegreeLE w s (F.realGradedSymbolPolynomialHom b ω hF w left).coord := by
  intro α hα
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w left.coord α i (by
    have hi := F.adaptedBasis_weight_le_step b ω hF i
    omega)

attribute [local irreducible] realChartSubstitute

theorem FullChartControlledFactors.exists_degree_bounded_chart
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
        DegreeLE (fullTaggedVariableWeight (X := X) J) s Echart.coord ∧
        DegreeLE (fun _ => 1) s Echart.coord ∧
        CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
          (F.realGradedSymbolPolynomialHom b ω hF
            (fullTaggedVariableWeight (X := X) J) right).coord := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hgrid⟩ := h
  let w := fullTaggedVariableWeight (X := X) J
  let E' : PolynomialGroup (X ⊕ (Σ j, J j))
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
    ⟨weightedDegreeTruncate w s E.coord⟩
  refine ⟨q, hq, hqB, E', ?_, ?_, degreeLE_weightedDegreeTruncate w s E.coord,
    degreeLE_one_weightedDegreeTruncate w (fullTaggedVariableWeight_pos J) s E.coord, hgrid⟩
  · have hd := F.realGradedSymbolPolynomialHom_degreeLE b ω hF
      (fullTaggedVariableWeight (X := X) J) left
    have he := realPolynomialChartSubstitution_truncate_of_degreeLE
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
      (fullTaggedVariableWeight (X := X) J)
      (normalizedRealPolynomialChart (fun i => (N i : ℝ)) (fullTaggedMajorTopCoordinates J poly))
      (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ))) s
      (F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left)
      E hchart hd
    exact he
  · exact CoefficientBound.weightedDegreeTruncate _ _ (fun _ => zero_lt_one)
      (Real.exp_pos budget).le hbound w s

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ : Type*} {ι L : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realPolynomialSymbolLift_coordinate (w : σ → ℕ)
    (x : F.RealPolynomialSymbolGroup w) (α : σ →₀ ℕ) (i : ι) :
    (b.baseChange ℝ).repr
      (coefficients (F.realPolynomialSymbolLift b ω hF w x).coord.val α) i =
      ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (coefficients (F.realGradedSymbolPolynomialHom b ω hF w x).coord α) i := by
  rw [F.realPolynomialSymbolLift_log, F.realSymbolRepresentative_coefficient_splitting,
    F.gradedBasisSplitting_real_coordinate]
  rfl

theorem realPolynomialSymbolLift_slow_iff (w : σ → ℕ)
    (T : σ → ℝ) (M : ℝ) (x : F.RealPolynomialSymbolGroup w) :
    F.PolynomialSlowBound b w T M (F.realPolynomialSymbolLift b ω hF w x) ↔
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
        (F.realGradedSymbolPolynomialHom b ω hF w x).coord := by
  unfold PolynomialSlowBound CoefficientBound
  simp only [F.realPolynomialSymbolLift_coordinate]

theorem realPolynomialSymbolLift_rationalGrid_iff (w : σ → ℕ)
    (q : ℕ) (x : F.RealPolynomialSymbolGroup w) :
    F.PolynomialRationalGrid b w q (F.realPolynomialSymbolLift b ω hF w x) ↔
      CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
        (F.realGradedSymbolPolynomialHom b ω hF w x).coord := by
  unfold PolynomialRationalGrid CoefficientGrid
  simp only [F.realPolynomialSymbolLift_coordinate]
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext (fun i => congrFun ha (α, i))⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

theorem coefficientBound_gradedBasisSplitting
    (T : σ → ℝ) (M : ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    CoefficientBound (b.baseChange ℝ) T M
      (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ↔
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M P := by
  unfold CoefficientBound
  simp only [coefficients_map, LinearMap.restrictScalars_apply,
    F.gradedBasisSplitting_real_coordinate]

attribute [local irreducible] realChartSubstitute

theorem realPolynomialSymbolLift_chart_pullback_bound [Fintype σ]
    {τ : Type*} (w : σ → ℕ) (v : τ → ℕ)
    (x : F.RealPolynomialSymbolGroup w)
    (f : σ → MvPolynomial σ ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hchart : (F.realGradedSymbolPolynomialHom b ω hF w x).coord =
      realChartSubstitute f P)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (T : τ → ℝ) (hT : ∀ i, 0 < T i) {A B : ℝ} {d : ℕ}
    (hP : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ)
      (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) d P)
    (hmass : ∀ i, realPolynomialMass
      (scaleMvPolynomialAxes T (MvPolynomial.aeval β (f i))) ≤ B) :
    F.PolynomialSlowBound b v T
      (((Fintype.card σ : ℝ) + 1) ^ d * A * B ^ d)
      (F.weightedAdaptedRealChartHom w v β hβ
        (F.realPolynomialSymbolLift b ω hF w x)) := by
  let S := (F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ
  have heq : (F.realPolynomialSymbolLift b ω hF w x).coord.val =
      realChartSubstitute f (VectorPolynomial.map (S.restrictScalars ℚ) P) := by
    rw [F.realPolynomialSymbolLift_log, F.realSymbolRepresentative_eq_map,
      realChartSubstitute_map]
    exact congrArg (VectorPolynomial.map (S.restrictScalars ℚ)) hchart
  change CoefficientBound (b.baseChange ℝ) T _
    (realChartSubstitute β (F.realPolynomialSymbolLift b ω hF w x).coord.val)
  rw [heq, realChartSubstitute_comp]
  exact CoefficientBound.realChartSubstitute_sharp (b.baseChange ℝ) T hT _
    ((F.coefficientBound_gradedBasisSplitting b ω hF _ _ P).mpr hP)
    hA hB (hdegree.map _) hmass

theorem FullChartControlledFactors.exists_fullPolynomial_lifts
    {m : ℕ} {X : Type} (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∃ (e r : (F.realification.adaptedPolynomialFiltration
          (fullTaggedVariableWeight (X := X) J)).Group)
        (Echart : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] L)),
        e = F.realPolynomialSymbolLift b ω hF _ left ∧
        r = F.realPolynomialSymbolLift b ω hF _ right ∧
        F.realPolynomialSymbolHom b ω hF _ e = left ∧
        F.realPolynomialSymbolHom b ω hF _ r = right ∧
        e.coord.val = realChartSubstitute
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (fullTaggedMajorTopCoordinates J poly)) Echart ∧
        CoefficientBound (b.baseChange ℝ) (fun _ => 1) (Real.exp budget) Echart ∧
        DegreeLE (fullTaggedVariableWeight (X := X) J) s Echart ∧
        DegreeLE (fun _ => 1) s Echart ∧
        F.PolynomialRationalGrid b (fullTaggedVariableWeight (X := X) J) q r := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_degree_bounded_chart F b ω hF J poly N left right h
  let S := (F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ
  refine ⟨q, hq, hqB, F.realPolynomialSymbolLift b ω hF _ left,
    F.realPolynomialSymbolLift b ω hF _ right,
    VectorPolynomial.map (S.restrictScalars ℚ) E.coord, rfl, rfl,
    F.realPolynomialSymbolHom_lift b ω hF _ left,
    F.realPolynomialSymbolHom_lift b ω hF _ right, ?_,
    (F.coefficientBound_gradedBasisSplitting b ω hF _ _ E.coord).mpr hbound,
    hweighted.map _, hdegree.map _,
    (F.realPolynomialSymbolLift_rationalGrid_iff b ω hF _ q right).mpr hgrid⟩
  rw [F.realPolynomialSymbolLift_log, F.realSymbolRepresentative_eq_map,
    realChartSubstitute_map]
  have hc := congrArg NilpotentLieBCHGroup.coord hchart
  rw [realPolynomialChartSubstitution_coord] at hc
  exact congrArg (VectorPolynomial.map (S.restrictScalars ℚ)) hc

theorem FullChartControlledFactors.restricted_left_slowBound
    {m : ℕ} {X τ : Type} [Fintype X]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v
      (fullTaggedVariableWeight (X := X) J i))
    (T : τ → ℝ) (hT : ∀ i, 0 < T i) {B : ℝ} (hB : 1 ≤ B)
    (hmass : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T
      (MvPolynomial.aeval β (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i))) ≤ B) :
    F.PolynomialSlowBound b v T
      (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget * B ^ s)
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight (X := X) J) v β hβ
        (F.realPolynomialSymbolLift b ω hF _ left)) := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_degree_bounded_chart F b ω hF J poly N left right h
  have hc := congrArg NilpotentLieBCHGroup.coord hchart
  rw [realPolynomialChartSubstitution_coord] at hc
  exact F.realPolynomialSymbolLift_chart_pullback_bound b ω hF _ v left _ E.coord hc
    β hβ T hT hbound (Real.exp_pos budget).le hB hdegree hmass

end Erdos3.NilpotentLieFiltration

end

end OAI
