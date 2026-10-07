import OAI.Combinatorics.Progressions.Probability.CanonicalCoverLaw
import OAI.Combinatorics.Progressions.Probability.EuclideanJetDensity
import OAI.Combinatorics.Progressions.Probability.LowJetDensity

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_affine_covered_density (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin q → K → ℤ) {P : ℝ}, 0 ≤ P →
    (Fintype.card K : ℝ) ≤ P →
    (∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ Real.exp P) →
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      [CompactSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
      (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
      (D : CoefficientTorus (K := K) U → ℝ), Continuous D →
      ∀ {B : ℝ}, (∀ x, D x ∈ Set.Icc (0 : ℝ) B) → (∫ x, D x ∂μ) = 1 →
      let E := coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k))
      let π := Set.rangeFactorization E
      let C := quotientIntegerCover (coefficientIntegerLattice U) d
      ∃ g : Set.range E → ℝ, Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) B) ∧
        Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
        (realDensityMeasure μ (fun x => D (C x))).map π = realDensityMeasure (μ.map π) g ∧
        ∀ {I F : Type*} [Fintype F]
          (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) {η : ℝ},
          (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
          ∀ (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (b : Option K → I → ℝ),
            ‖affineCubeFourierProjection U root difference frequency p c b -
              (g (π (affineCoefficientCoverSample U p hm d b)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hbudget⟩ := exists_geometric_positive_cover_budget m q
  refine ⟨A, hA, ?_⟩
  intro K _ root difference P hP hK hsite
  let site := fun s k => affineSite root difference s (some k)
  obtain ⟨d, T, hd, hT, hbound⟩ := exists_common_integer_site_residual
    (fun j : Fin m => boundedSiteMatrix (j.val + 1) site) (fun _ => exponentialSiteHeight m P)
    (fun _ => exponentialSiteHeight_pos m P)
    (fun j => boundedSiteMatrix_height_of_exp m (Nat.succ_le_of_lt j.isLt) site hsite)
  have hperiod := hbound (geometricSiteBudget_nonneg m q hP)
    (fun j => boundedCoefficientExponent_card_le_geometricSiteBudget m q
      (Nat.succ_le_of_lt j.isLt) hP hK)
    (cubeSites_card_le_geometricSiteBudget m q hP)
    (fun _ => (exponentialSiteHeight_le m hP).trans
      (Real.exp_le_exp.mpr (degree_mul_le_geometricSiteBudget m q hP)))
  refine ⟨d, hd, ?_, ?_⟩
  · exact hperiod.trans (Real.exp_le_exp.mpr (by simpa only [Fintype.card_fin] using hbudget P hP))
  intro J _ U _ _ _ _ _ μ _ _ D hD B hcap hmass E π C
  let R := coefficientSiteResidual U site (fun _ => d) T
  let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => d) T
  obtain ⟨g, hgc, hgb, hgi, hgmass, hg, hlaw⟩ :=
    exists_covered_coefficient_density U site d hd T (fun j x => hT j x) μ D hD hcap hmass
  refine ⟨g, hgc, hgb, hgi, hgmass, hlaw, ?_⟩
  intro I F _ frequency c η happrox p hp hm b
  have hfactor (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
      (coefficientArrayFunctional U frequency).comp R = 0 ↔
        affineCubeModeFactors U root difference frequency := by
    change (coefficientArrayFunctional U frequency).comp
      (coefficientSiteResidual U site (fun _ => d) T) = 0 ↔ _
    rw [coefficientSiteResidual_zero_iff U site (fun _ => d) T (fun _ => hd) (fun j x => hT j x),
      affineCubeModeFactors_iff_bounded]
  have hb (x) : ‖D x‖ ≤ B := by rw [Real.norm_of_nonneg (hcap x).1]; exact (hcap x).2
  have he := coefficientTorusFourierProjection_approx_residualAverage U R hR root difference hfactor
    frequency c μ D happrox (affineSampleCoefficientTorus U p hm b)
    (coefficientResidual_section_integrable U R hR μ D hD hb _)
  have hvalue := hg (affineCoefficientCoverSample U p hm d b)
  rw [affineCoefficientCoverSample_projection U p hm d hd b] at hvalue
  rw [hvalue]
  simpa only [coefficientTorusCharacter_sample U _ p hp hm b, affineCubeFourierProjection] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped Classical

theorem exists_affine_covered_euclidean_density (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin q → K → ℤ) {P : ℝ}, 0 ≤ P →
    (Fintype.card K : ℝ) ≤ P →
    (∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ Real.exp P) →
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
      ∀ (a : ℤ), a ≠ 0 →
      integerScalarLattice (Fin q) a ≤ (Matrix.of difference).mulVecLin.range →
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      [CompactSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
      (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (D : CoefficientTorus (K := K) U → ℝ), Continuous D →
      ∀ {B : ℝ}, (∀ x, D x ∈ Set.Icc (0 : ℝ) B) → (∫ x, D x ∂μ) = 1 →
      let F := euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      let C := quotientIntegerCover (coefficientIntegerLattice U) d
      let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
      ∃ f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ,
        Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) B) ∧ Integrable f ξ ∧
        (∫ z, f z ∂ξ) = 1 ∧
        (realDensityMeasure μ (fun x => D (C x))).map F = realDensityMeasure ξ f ∧
        ∀ {I G : Type*} [Fintype G]
          (frequency : G → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : G → ℂ) {η : ℝ},
          (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
          ∀ (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (b : Option K → I → ℝ),
            ‖affineCubeFourierProjection U root difference frequency p c b -
              (f (F (affineCoefficientCoverSample U p hm d b)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hcover⟩ := exists_affine_covered_density m q
  refine ⟨A, hA, ?_⟩
  intro K _ root difference P hP hK hsite
  obtain ⟨d, hd, hdb, hcover⟩ := hcover root difference hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro a ha hperiod J _ U _ _ _ _ _ μ _ _ ν _ _ D hD B hcap hmass F C ξ
  obtain ⟨g, hgc, hgb, _, hgmass, hglaw, hgapprox⟩ := hcover U μ D hD hcap hmass
  obtain ⟨hfc, hfb, hfi, hfmass, hvalue, hflaw⟩ := siteImage_density_euclideanJet U root
    (Matrix.of difference) a ha hperiod μ ν (realDensityMeasure μ (fun x => D (C x)))
    g hgc hgb hgmass hglaw
  refine ⟨_, hfc, hfb, hfi, hfmass, hflaw, ?_⟩
  intro I G _ frequency c η happrox p hp hm b
  have he := hvalue (Set.rangeFactorization
    (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference)))
    (affineCoefficientCoverSample U p hm d b))
  change (g ((euclideanSiteImageHomeomorph U root (Matrix.of difference) a ha hperiod).symm
    (F (affineCoefficientCoverSample U p hm d b)))) = _ at he
  rw [he]
  exact hgapprox frequency c happrox p hp hm b

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped Classical

theorem exists_affine_covered_jet_density (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin q → K → ℤ) {P : ℝ}, 0 ≤ P →
    (Fintype.card K : ℝ) ≤ P →
    (∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ Real.exp P) →
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
      ∀ (a : ℤ), a ≠ 0 →
      integerScalarLattice (Fin q) a ≤ (Matrix.of difference).mulVecLin.range →
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      [CompactSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
      [∀ j, MeasurableSpace (SubspaceArrayTorus (BoundedBooleanJet (Fin q) (j.val + 1)) (U j))]
      [∀ j, BorelSpace (SubspaceArrayTorus (BoundedBooleanJet (Fin q) (j.val + 1)) (U j))]
      (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
      (ν : ∀ j, Measure (SubspaceArrayTorus (BoundedBooleanJet (Fin q) (j.val + 1)) (U j)))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (D : CoefficientTorus (K := K) U → ℝ), Continuous D →
      ∀ {B : ℝ}, (∀ x, D x ∈ Set.Icc (0 : ℝ) B) → (∫ x, D x ∂μ) = 1 →
      let F := coefficientBooleanJetTorusMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      let C := quotientIntegerCover (coefficientIntegerLattice U) d
      ∃ f : LowBooleanJetTorus (Fin q) U → ℝ, Continuous f ∧
        (∀ z, f z ∈ Set.Icc (0 : ℝ) B) ∧ Integrable f (Measure.pi ν) ∧
        (∫ z, f z ∂Measure.pi ν) = 1 ∧
        (realDensityMeasure μ (fun x => D (C x))).map F = realDensityMeasure (Measure.pi ν) f ∧
        ∀ {I G : Type*} [Fintype G]
          (frequency : G → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : G → ℂ) {η : ℝ},
          (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
          ∀ (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (b : Option K → I → ℝ),
            ‖affineCubeFourierProjection U root difference frequency p c b -
              (f (F (affineCoefficientCoverSample U p hm d b)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hcover⟩ := exists_affine_covered_density m q
  refine ⟨A, hA, ?_⟩
  intro K _ root difference P hP hK hsite
  obtain ⟨d, hd, hdb, hcover⟩ := hcover root difference hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro a ha hperiod J _ U _ _ _ _ _ _ _ μ _ _ ν _ _ D hD B hcap hmass F C
  obtain ⟨g, hgc, hgb, _, hgmass, hglaw, hgapprox⟩ := hcover U μ D hD hcap hmass
  obtain ⟨f, hfc, hfb, hfi, hfmass, hvalue, hflaw⟩ := siteImage_density_lowJet U root
    (Matrix.of difference) a ha hperiod μ ν (realDensityMeasure μ (fun x => D (C x)))
    g hgc hgb hgmass hglaw
  refine ⟨f, hfc, hfb, hfi, hfmass, hflaw, ?_⟩
  intro I G _ frequency c η happrox p hp hm b
  have he := hvalue (Set.rangeFactorization
    (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference)))
    (affineCoefficientCoverSample U p hm d b))
  change f (F (affineCoefficientCoverSample U p hm d b)) = _ at he
  rw [he]
  exact hgapprox frequency c happrox p hp hm b

end Erdos3.BooleanCubeKernel

end

end OAI
