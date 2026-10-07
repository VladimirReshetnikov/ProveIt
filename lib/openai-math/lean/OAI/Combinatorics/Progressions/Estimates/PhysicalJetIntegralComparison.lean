import OAI.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_physical_jet_integral_comparison (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (Fin q →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (cover : ℕ) (_hcover : 0 < cover) (_hcoverP : (cover : ℝ) ≤ Real.exp P)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P + A) ^ A) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin q)) X stride)) (_hcells : cells.Nonempty)
    (V : Option (Fin q) × X → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (g : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (_hg : Integrable g
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))))
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ y, ‖(g (standardPhysicalJetMap U y) : ℂ) -
      coefficientTorusFourierSum U frequency c y‖ ≤ η),
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      |selectedResidueDensityMass stride cells V
        (fun z => g (physicalCubeEuclideanSample U cover p hm (standardPhysicalCubeOutput z))) -
          (∫ y, g y ∂(Measure.pi (fun j =>
            Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))))| ≤ 2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_cover_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro X _ _ J _ F _ P hP hn hdim U _ _ _ μ _ _ ν _ _ C hC hCP frequency hbound c B
    hB hBP hcoefficients p hp hm cover hcover hcoverP stride hs R S ρ ε hS hSP hρ hε
    hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth g hg η hη happrox
  have hpull := standardPhysicalJetMap_measurePreserving U μ ν
  have hg' := hpull.integrable_comp_of_integrable hg
  have hmass : (∫ y, g (standardPhysicalJetMap U y) ∂μ) =
      ∫ y, g y ∂(Measure.pi (fun j =>
        Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))) := by
    have hgm : AEStronglyMeasurable g (Measure.map (standardPhysicalJetMap U) μ) := by
      rw [hpull.map_eq]
      exact hg.aestronglyMeasurable
    simpa only [hpull.map_eq] using (integral_map hpull.measurable.aemeasurable hgm).symm
  obtain ⟨hZ, he⟩ := hcomparison hP hn hdim U μ hC hCP frequency hbound c hB hBP
    hcoefficients p hp hm cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR cells hcells V hV hwidth
    (fun y => (g (standardPhysicalJetMap U y) : ℂ)) hg'.ofReal hη happrox
  refine ⟨hZ, ?_⟩
  rw [integral_complex_ofReal, hmass] at he
  simp_rw [coefficientCoverSample_standardPhysicalJet U cover p hp hm] at he
  rw [← selectedResidueDensityMass_complex stride cells V hV hZ,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he
  exact he

end Erdos3.BooleanCubeKernel

namespace Erdos3

open scoped BigOperators

theorem selectedResidueDensityMass_mono {K X : Type*} [Fintype K] [Fintype X]
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern K X stride))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    {f g : (K × X → ℤ) → ℝ} (hfg : ∀ z, f z ≤ g z) :
    selectedResidueDensityMass stride cells V f ≤ selectedResidueDensityMass stride cells V g := by
  rw [← selectedResidueFiniteLaw_densityMass stride cells V hV hZ f,
    ← selectedResidueFiniteLaw_densityMass stride cells V hV hZ g]
  exact (selectedResidueFiniteLaw stride cells V hV hZ).mean_mono (fun z => hfg z.val)

theorem selectedResidueDensityMass_le_of_majorant {K X : Type*} [Fintype K] [Fintype X]
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern K X stride))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    {f g : (K × X → ℤ) → ℝ} (hfg : ∀ z, f z ≤ g z)
    {M E t : ℝ} (hM : t ≤ M)
    (hmean : |selectedResidueDensityMass stride cells V g - t| ≤ E) :
    selectedResidueDensityMass stride cells V f ≤ M + E := by
  have hle := selectedResidueDensityMass_mono stride cells V hV hZ hfg
  have he := (abs_le.mp hmean).2
  linarith

end Erdos3

end

end OAI
