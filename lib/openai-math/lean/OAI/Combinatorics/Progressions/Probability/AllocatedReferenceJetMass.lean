import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
import OAI.Combinatorics.Progressions.Fourier.AllocatedJetFourierData
import OAI.Combinatorics.Progressions.Lattices.CoefficientLatticeCompact

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_physical_jet_density_mass (m q : ℕ) :
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
    (_hgmass : (∫ y, g y ∂(Measure.pi (fun j =>
      Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j)))) = 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ y, ‖(g (standardPhysicalJetMap U y) : ℂ) -
      coefficientTorusFourierSum U frequency c y‖ ≤ η),
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      |selectedResidueDensityMass stride cells V
        (fun z => g (physicalCubeEuclideanSample U cover p hm (standardPhysicalCubeOutput z))) - 1| ≤
          2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_cover_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro X _ _ J _ F _ P hP hn hdim U _ _ _ μ _ _ ν _ _ C hC hCP frequency hbound c B
    hB hBP hcoefficients p hp hm cover hcover hcoverP stride hs R S ρ ε hS hSP hρ hε
    hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth g hg hgmass η hη happrox
  obtain ⟨hg', hmass⟩ := standardPhysicalJetMap_density_mass U μ ν g hg hgmass
  obtain ⟨hZ, he⟩ := hcomparison hP hn hdim U μ hC hCP frequency hbound c hB hBP
    hcoefficients p hp hm cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR cells hcells V hV hwidth
    (fun y => (g (standardPhysicalJetMap U y) : ℂ)) hg'.ofReal hη happrox
  refine ⟨hZ, ?_⟩
  rw [integral_complex_ofReal, hmass, Complex.ofReal_one] at he
  simp_rw [coefficientCoverSample_standardPhysicalJet U cover p hp hm] at he
  rw [← selectedResidueDensityMass_complex stride cells V hV hZ,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he
  exact he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_physical_jet_singleton_window_mass (m q : ℕ) :
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
    (residue : ColumnResiduePattern (Option (Fin q)) X stride)
    (V : Option (Fin q) × X → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (_hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z)
    (g : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (_hg0 : ∀ y, 0 ≤ g y)
    (_hg : Integrable g
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))))
    (_hgmass : (∫ y, g y ∂(Measure.pi (fun j =>
      Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j)))) = 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ y, ‖(g (standardPhysicalJetMap U y) : ℂ) -
      coefficientTorusFourierSum U frequency c y‖ ≤ η)
    (window : Finset (X → (Unit ⊕ Fin q) → ℤ))
    (_hresidue : ∀ v ∈ window, columnResiduePattern stride (standardPhysicalCubeFrame v) = residue)
    (_hinner : ∀ v ∈ window, ∀ i, |(standardPhysicalCubeFrame v i : ℝ) / V i| ≤ 1 / 2),
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {residue} V z,
      (∑ v ∈ window, g (physicalCubeEuclideanSample U cover p hm v)) ≤
        ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
          (∏ i, residueProfileWidth stride V i) /
          (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) * (1 + 2 * η + ε) := by
  obtain ⟨A, hA, hmass⟩ := exists_physical_jet_density_mass m q
  refine ⟨A, hA, ?_⟩
  intro X _ _ J _ F _ P hP hn hdim U _ _ _ μ _ _ ν _ _ C hC hCP frequency hbound c B
    hB hBP hcoefficients p hp hm cover hcover hcoverP stride hs R S ρ ε hS hSP hρ hε
    hρP hεP hstride H hsize hrank hR residue V hV hwidth hscale g hg0 hg hgmass η hη happrox
    window hresidue hinner
  obtain ⟨hZ, hclose⟩ := hmass hP hn hdim U μ ν hC hCP frequency hbound c hB hBP
    hcoefficients p hp hm cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR {residue} (Finset.singleton_nonempty _) V hV hwidth g hg hgmass hη happrox
  refine ⟨hZ, ?_⟩
  let D := fun z : Option (Fin q) × X → ℤ =>
    g (physicalCubeEuclideanSample U cover p hm (standardPhysicalCubeOutput z))
  let frames := window.image standardPhysicalCubeFrame
  have hresidue' : ∀ z ∈ frames, columnResiduePattern stride z = residue := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hresidue v hv
  have hinner' : ∀ z ∈ frames, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hinner v hv
  have hraw := selectedResidueDensityMass_singleton_window_bound stride hs residue V hV hscale
    hZ D (fun z => hg0 _) frames hresidue' hinner'
  have hsum : (∑ z ∈ frames, D z) = ∑ v ∈ window, g (physicalCubeEuclideanSample U cover p hm v) := by
    dsimp only [frames]
    rw [Finset.sum_image]
    · simp only [D, standardPhysicalCubeOutput_frame]
    · intro v _ w _ he
      exact standardPhysicalCubeFrame_injective he
  rw [hsum] at hraw
  have hQ : 0 ≤ ∏ i, residueProfileWidth stride V i :=
    Finset.prod_nonneg (fun i _ => (residueProfileWidth_pos stride V hs hV i).le)
  have hfactor : 0 ≤ (3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
      (∏ i, residueProfileWidth stride V i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) :=
    div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hQ)
      (pow_pos smoothProbabilityProfile_pos_zero _).le
  have hupper : selectedResidueDensityMass stride {residue} V D ≤ 1 + 2 * η + ε := by
    have h := (abs_le.mp hclose).2
    change selectedResidueDensityMass stride {residue} V D - 1 ≤ 2 * η + ε at h
    linarith
  exact hraw.trans (mul_le_mul_of_nonneg_left hupper hfactor)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalWindow_sum_le_sampled_mass {X : Type*} [Fintype X] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (residue : ColumnResiduePattern (Option (Fin q)) X stride)
    (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {residue} V z)
    (f : (X → (Unit ⊕ Fin q) → ℤ) → ℝ) (hf : ∀ v, 0 ≤ f v)
    (window : Finset (X → (Unit ⊕ Fin q) → ℤ))
    (hresidue : ∀ v ∈ window, columnResiduePattern stride (standardPhysicalCubeFrame v) = residue)
    (hinner : ∀ v ∈ window, ∀ i, |(standardPhysicalCubeFrame v i : ℝ) / V i| ≤ 1 / 2) :
    (∑ v ∈ window, f v) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
          selectedResidueDensityMass stride {residue} V (fun z => f (standardPhysicalCubeOutput z)) := by
  let frames := window.image standardPhysicalCubeFrame
  have hr : ∀ z ∈ frames, columnResiduePattern stride z = residue := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hresidue v hv
  have hi : ∀ z ∈ frames, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hinner v hv
  have h := selectedResidueDensityMass_singleton_window_bound stride hs residue V hV hscale hZ
    (fun z => f (standardPhysicalCubeOutput z)) (fun z => hf _) frames hr hi
  have he : (∑ z ∈ frames, f (standardPhysicalCubeOutput z)) = ∑ v ∈ window, f v := by
    dsimp only [frames]
    rw [Finset.sum_image]
    · simp only [standardPhysicalCubeOutput_frame]
    · intro v _ w _ he
      exact standardPhysicalCubeFrame_injective he
  rwa [he] at h

theorem physicalReconstruction_sum_le_sampled_mass {X K : Type*} [Fintype X] [Fintype K] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ)
    (residue : ColumnResiduePattern (Option K) X stride)
    (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (hscale : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (f : (X → (Unit ⊕ Fin q) → ℤ) → ℝ) (hf : ∀ v, 0 ≤ f v) :
    let r := boundedColumnResidueRepresentative stride residue
    let target := columnResiduePattern stride
      (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 r))
    let V := referenceJetEnvelopeWidths (q := q) stride H
    0 < ∑' z, selectedResidueSmoothWeight stride {target} V z →
    (∑ v ∈ spatialWindow H 4, f (physicalResidueReconstruction root D 0 r stride v)) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
          selectedResidueDensityMass stride {target} V (fun z => f (standardPhysicalCubeOutput z)) := by
  intro r target V hZ
  let window := (spatialWindow H 4).image (physicalResidueReconstruction root D 0 r stride)
  have hr : ∀ k x, |(r (k,x) : ℝ)| ≤ stride x := by
    intro k x
    have h := boundedColumnResidueRepresentative_bounds stride hs residue (k,x)
    rw [abs_of_nonneg (by exact_mod_cast h.1 : (0 : ℝ) ≤ r (k,x))]
    exact_mod_cast h.2.le
  have hoffset := physicalCube_zero_residue_bound root D stride r hr H hrows
  have hres : ∀ v ∈ window, columnResiduePattern stride (standardPhysicalCubeFrame v) = target := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact physicalResidueReconstruction_columnResidue root D 0 r stride w
  have hin : ∀ v ∈ window, ∀ i, |(standardPhysicalCubeFrame v i : ℝ) / V i| ≤ 1 / 2 := by
    intro v hv i
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact physicalResidueReconstruction_envelope root D stride hs r H hH hoffset hw i
  have hsc : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z := by
    intro z
    change _ ≤ residueProfileWidth stride (referenceJetEnvelopeWidths stride H) z
    rw [referenceJetEnvelopeWidths_residue stride hs H]
    exact hscale z.2
  have h := physicalWindow_sum_le_sampled_mass stride hs target V
    (referenceJetEnvelopeWidths_pos stride hs H hH) hsc hZ f hf window hres hin
  have he : (∑ v ∈ window, f v) =
      ∑ v ∈ spatialWindow H 4, f (physicalResidueReconstruction root D 0 r stride v) := by
    dsimp only [window]
    exact Finset.sum_image (fun v _ w _ he => physicalResidueReconstruction_injective root D 0 r stride hs he)
  rwa [he] at h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_reference_reconstruction_jet_mass (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K]
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
    (N : X → ℝ) (_hsize : ∀ x, Real.exp ((P + A) ^ A) ≤ N x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) N R (U j) (p j))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (residue : ColumnResiduePattern (Option K) X stride)
    (H : X → ℝ) (_hH : ∀ x, 0 < H x)
    (_hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (_hwidth : ∀ x, ρ * N x ≤ 20 * (stride x : ℝ) * H x)
    (_hscale : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (g : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (_hg0 : ∀ y, 0 ≤ g y)
    (_hg : Integrable g
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))))
    (_hgmass : (∫ y, g y ∂(Measure.pi (fun j =>
      Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j)))) = 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ y, ‖(g (standardPhysicalJetMap U y) : ℂ) -
      coefficientTorusFourierSum U frequency c y‖ ≤ η),
    (∑ v ∈ spatialWindow H 4, g (physicalCubeEuclideanSample U cover p hm
        (physicalResidueReconstruction root D base
          (boundedColumnResidueRepresentative stride residue) stride v))) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := q) stride H) i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) * (1 + 2 * η + ε) := by
  obtain ⟨A, hA, hmass⟩ := exists_physical_jet_singleton_window_mass m q
  refine ⟨A, hA, ?_⟩
  intro X K _ _ _ J _ F _ P hP hn hdim U _ _ _ μ _ _ ν _ _ C hC hCP frequency hbound c B
    hB hBP hcoefficients p hp hm cover hcover hcoverP stride hs R S ρ ε hS hSP hρ hε
    hρP hεP hstride N hsize hrank hR root D base residue H hH hrows hwidth hscale
    g hg0 hg hgmass η hη happrox
  let r := boundedColumnResidueRepresentative stride residue
  let reconstruct := physicalResidueReconstruction root D 0 r stride
  let window := (spatialWindow H 4).image reconstruct
  let targetResidue := columnResiduePattern stride
    (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 r))
  let V := referenceJetEnvelopeWidths (q := q) stride H
  have hresidue : ∀ v ∈ window, columnResiduePattern stride (standardPhysicalCubeFrame v) = targetResidue := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact physicalResidueReconstruction_columnResidue root D 0 r stride w
  have hr : ∀ k x, |(r (k,x) : ℝ)| ≤ stride x := by
    intro k x
    have h := boundedColumnResidueRepresentative_bounds stride hs residue (k,x)
    rw [abs_of_nonneg (by exact_mod_cast h.1 : (0 : ℝ) ≤ r (k,x))]
    exact_mod_cast h.2.le
  have hoffset := physicalCube_zero_residue_bound root D stride r hr H hrows
  have hinner : ∀ v ∈ window, ∀ i, |(standardPhysicalCubeFrame v i : ℝ) / V i| ≤ 1 / 2 := by
    intro v hv i
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact physicalResidueReconstruction_envelope root D stride hs r H hH hoffset hw i
  have hV := referenceJetEnvelopeWidths_pos (q := q) stride hs H hH
  have hscale' : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z := by
    intro z
    change 8 * (probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth stride (referenceJetEnvelopeWidths stride H) z
    rw [referenceJetEnvelopeWidths_residue stride hs H]
    exact hscale z.2
  obtain ⟨_, hsum⟩ := hmass hP hn hdim U μ ν hC hCP frequency hbound c hB hBP hcoefficients
    (fun j => translate (fun x => (base x : ℝ)) (p j))
    (fun j => degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
    (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j))
    cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride N hsize
    (fun j => (hasLayerSamplingRank_translate_iff _ _ N R (U j) (p j) (hp j)).mpr (hrank j))
    hR targetResidue V hV (fun z => hwidth z.2) hscale' g hg0 hg hgmass hη happrox
    window hresidue hinner
  have he := physicalResidueReconstruction_jet_sum U cover p hm root D base r stride hs g
    (spatialWindow H 4)
  exact he.ge.trans hsum

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem referenceJetEnvelope_volume {X : Type*} [Fintype X] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H : X → ℝ) :
    ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
      (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := q) stride H) i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) =
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (∏ x, ∏ _i : Unit ⊕ Fin q, H x) := by
  have hprod : (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := q) stride H) i) =
      20 ^ Fintype.card (Option (Fin q) × X) * (∏ i : Option (Fin q) × X, H i.2) := by
    simp_rw [referenceJetEnvelopeWidths_residue stride hs H]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
  have hcoord : (∏ i : Option (Fin q) × X, H i.2) = ∏ x, ∏ _i : Unit ⊕ Fin q, H x := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_option,
      Fintype.card_fin, Fintype.card_sum, Fintype.card_unique, Nat.add_comm]
  rw [hprod, hcoord, ← mul_assoc, ← mul_pow]
  norm_num only [show (3 / 2 : ℝ) * 20 = 30 by norm_num]
  rw [mul_div_right_comm, ← div_pow]

theorem referenceJetEnvelope_anisotropic_volume {X : Type*} [Fintype X] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H T : X → ℝ)
    {W L : ℝ} (hL : L ≠ 0) (hscale : ∀ x, H x = (1 + W) * T x) :
    ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
      (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := q) stride H) i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) =
    ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (((1 + W) / L) ^ q) ^ Fintype.card X) *
      (∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i) := by
  rw [referenceJetEnvelope_volume stride hs H, physicalSpatial_uniform_volume H T hL hscale]
  simp only [Fintype.card_fin, mul_assoc]

theorem reference_density_spatial_error {K X Y : Type*} [Fintype K] [Fintype X] {q : ℕ}
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option K) X stride))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (H T : X → ℝ) {L : ℝ}
    (hA : 0 < ∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)
    (point : (X → (Unit ⊕ Fin q) → ℤ) → Y) (g : Y → ℝ) (hg : ∀ y, 0 ≤ g y)
    (test : (X → (Unit ⊕ Fin q) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1)
    {E C : ℝ} (hE : 0 ≤ E)
    (hmass : ∀ a : cells, (∑ v ∈ spatialWindow H 4, g (point
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride a.val) stride v))) ≤
        C * (∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)) :
    (∑ a : cells, selectedResidueCellWeight stride cells V a *
      ((E / (∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)) *
        ∑ v ∈ spatialWindow H 4,
          ‖test (physicalResidueReconstruction root D base
            (boundedColumnResidueRepresentative stride a.val) stride v)‖ *
          g (point (physicalResidueReconstruction root D base
            (boundedColumnResidueRepresentative stride a.val) stride v)))) ≤ E * C := by
  let A := ∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i
  have hbound (a : cells) : (E / A) * (∑ v ∈ spatialWindow H 4,
      ‖test (physicalResidueReconstruction root D base
        (boundedColumnResidueRepresentative stride a.val) stride v)‖ *
      g (point (physicalResidueReconstruction root D base
        (boundedColumnResidueRepresentative stride a.val) stride v))) ≤ E * C := by
    have hs : (∑ v ∈ spatialWindow H 4,
        ‖test (physicalResidueReconstruction root D base
          (boundedColumnResidueRepresentative stride a.val) stride v)‖ *
        g (point (physicalResidueReconstruction root D base
          (boundedColumnResidueRepresentative stride a.val) stride v))) ≤ C * A := by
      apply le_trans _ (hmass a)
      apply Finset.sum_le_sum
      intro v _
      exact (mul_le_mul_of_nonneg_right (htest _) (hg _)).trans_eq (one_mul _)
    have h := mul_le_mul_of_nonneg_left hs (div_nonneg hE hA.le)
    have hA0 : A ≠ 0 := hA.ne'
    have he : E / A * (C * A) = E * C := by field_simp [hA0]
    exact h.trans_eq he
  calc
    _ ≤ ∑ a : cells, selectedResidueCellWeight stride cells V a * (E * C) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hbound a)
        (selectedResidueCellWeight_nonneg stride cells V a))
    _ = (∑ a : cells, selectedResidueCellWeight stride cells V a) * (E * C) :=
      (Finset.sum_mul _ _ _).symm
    _ = E * C := by rw [selectedResidueCellWeight_sum stride cells V hV hZ, one_mul]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def coarseReferenceMassConstant (q : ℕ) (X : Type*) [Fintype X]
    (W L : ℝ) : ℝ :=
  4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
    (((1 + W) / L) ^ q) ^ Fintype.card X

theorem coarse_reference_density_spatial_error {K X Y : Type*} [Fintype K] [Fintype X] {q : ℕ}
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option K) X stride))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (H T : X → ℝ) {W L : ℝ} (hL : L ≠ 0) (hscale : ∀ x, H x = (1 + W) * T x)
    (hA : 0 < ∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)
    (point : (X → (Unit ⊕ Fin q) → ℤ) → Y) (g : Y → ℝ) (hg : ∀ y, 0 ≤ g y)
    (test : (X → (Unit ⊕ Fin q) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1)
    {E : ℝ} (hE : 0 ≤ E)
    (hmass : ∀ a : cells, (∑ v ∈ spatialWindow H 4, g (point
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride a.val) stride v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
          (∏ x, ∏ _i : Unit ⊕ Fin q, H x)) :
    (∑ a : cells, selectedResidueCellWeight stride cells V a *
      ((E / (∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)) *
        ∑ v ∈ spatialWindow H 4,
          ‖test (physicalResidueReconstruction root D base
            (boundedColumnResidueRepresentative stride a.val) stride v)‖ *
          g (point (physicalResidueReconstruction root D base
            (boundedColumnResidueRepresentative stride a.val) stride v)))) ≤
      E * coarseReferenceMassConstant q X W L := by
  apply reference_density_spatial_error stride cells V hV hZ root D base H T hA point g hg test htest hE
  intro a
  have h := hmass a
  rw [physicalSpatial_uniform_volume H T hL hscale] at h
  simpa only [coarseReferenceMassConstant, Fintype.card_fin, mul_assoc] using h

theorem coarse_reference_mean_spatial_budget {K X Y Ω : Type*}
    [Fintype K] [Fintype X] [Fintype Ω] {q : ℕ}
    (weights : FiniteProbabilityWeights Ω)
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option K) X stride))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (H T : X → ℝ) {W L : ℝ} (hL : L ≠ 0) (hscale : ∀ x, H x = (1 + W) * T x)
    (hA : 0 < ∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)
    (point : (X → (Unit ⊕ Fin q) → ℤ) → Y) (g : Ω → Y → ℝ)
    (hg : ∀ w y, 0 ≤ g w y)
    (test : (X → (Unit ⊕ Fin q) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1)
    {E offset Z : ℝ} (hE : 0 ≤ E) (hpos : 0 < Z)
    (hmass : ∀ w, weights.weight w ≠ 0 → ∀ a : cells,
      (∑ v ∈ spatialWindow H 4, g w (point (physicalResidueReconstruction root D base
        (boundedColumnResidueRepresentative stride a.val) stride v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
          (∏ x, ∏ _i : Unit ⊕ Fin q, H x)) :
    weights.mean (fun w => offset +
      (∑ a : cells, selectedResidueCellWeight stride cells V a *
        ((E / (∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)) *
          ∑ v ∈ spatialWindow H 4,
            ‖test (physicalResidueReconstruction root D base
              (boundedColumnResidueRepresentative stride a.val) stride v)‖ *
            g w (point (physicalResidueReconstruction root D base
              (boundedColumnResidueRepresentative stride a.val) stride v)))) / Z) ≤
      offset + E * coarseReferenceMassConstant q X W L / Z := by
  rw [← weights.mean_const (offset + E * coarseReferenceMassConstant q X W L / Z)]
  apply weights.mean_mono_on_support
  intro w hw
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_right
    (coarse_reference_density_spatial_error stride cells V hV hZ root D base H T hL
      hscale hA point (g w) (hg w) test htest hE (hmass w hw)) hpos.le

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_coarse_reference_jet_mass (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (frequency : F → ∀ j, (Fin q →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j e, e.degree ≤ j.val + 1 → ∀ t,
      |(frequency a j e t : ℝ)| ≤ Real.exp P)
    (c : F → ℂ) (_hcoefficients : (∑ a, ‖c a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (cover : ℕ) (_hcover : 0 < cover) (_hcoverP : (cover : ℝ) ≤ Real.exp P)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R τ : ℝ} (_hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ Real.exp P)
    (N : X → ℝ) (_hsize : ∀ x, Real.exp ((P + A) ^ A) ≤ N x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) N R (U j) (p j))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (residue : ColumnResiduePattern (Option K) X stride)
    (H : X → ℝ) (_hH : ∀ x, 0 < H x)
    (_hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (_hwidth : ∀ x, τ * N x ≤ 20 * (stride x : ℝ) * H x)
    (_hscale : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (g : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (_hg0 : ∀ y, 0 ≤ g y)
    (_hg : Integrable g
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))))
    (_hgmass : (∫ y, g y ∂(Measure.pi (fun j =>
      Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j)))) = 1)
    (_happrox : ∀ y : CoefficientTorus (K := Fin q) U,
      ‖(g (standardPhysicalJetMap U y) : ℂ) - coefficientTorusFourierSum U frequency c y‖ ≤ 1),
    (∑ v ∈ spatialWindow H 4, g (physicalCubeEuclideanSample U cover p hm
        (physicalResidueReconstruction root D base
          (boundedColumnResidueRepresentative stride residue) stride v))) ≤
      (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
        (∏ x, ∏ _i : Unit ⊕ Fin q, H x) := by
  obtain ⟨A, hA, hmass⟩ := exists_reference_reconstruction_jet_mass m q
  refine ⟨A, hA, ?_⟩
  intro X K _ _ _ J _ F _ P hP hn hdim U _ ν _ _ frequency hbound c hcoefficients
    p hp hm cover hcover hcoverP stride hs R τ hτ hτP hstride N hsize hrank hR
    root D base residue H hH hrows hwidth hscale g hg0 hg hgmass happrox
  let _ := coefficientTorus_compact_of_lattice (K := Fin q) U
  let _ : MeasurableSpace (CoefficientTorus (K := Fin q) U) := borel _
  let _ : BorelSpace (CoefficientTorus (K := Fin q) U) := ⟨rfl⟩
  have he := (Real.exp_pos P).le
  have h := hmass hP hn hdim U (probabilityAddHaar _) ν he le_rfl frequency hbound c
    he le_rfl hcoefficients p hp hm cover hcover hcoverP stride hs he le_rfl hτ
    (show (0 : ℝ) < 1 by norm_num) hτP (by simpa using Real.one_le_exp hP)
    hstride N hsize hrank hR root D base residue H hH hrows hwidth hscale
    g hg0 hg hgmass (show (0 : ℝ) ≤ 1 by norm_num) happrox
  rw [referenceJetEnvelope_volume stride hs H] at h
  convert h using 1
  ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalReconstruction_normalized_mass_le {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (root : K → ℤ) (D : Matrix (Fin dim) K ℤ)
    (residue : ColumnResiduePattern (Option K) X stride) (base : X → ℤ)
    (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L) (hscale : ∀ x, H x = (1 + W) * T x)
    (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (hscaleLarge : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (f : (X → (Unit ⊕ Fin dim) → ℤ) → ℝ) (hf : ∀ v, 0 ≤ f v) {M : ℝ} :
    let r := boundedColumnResidueRepresentative stride residue
    let target := columnResiduePattern stride (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 r))
    let V := referenceJetEnvelopeWidths (q := dim) stride H
    (∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {target} V z,
      selectedResidueDensityMass stride {target} V
        (fun z => f (translatePhysicalCube base (standardPhysicalCubeOutput z))) ≤ M) →
    (∑ v ∈ spatialWindow H 4, f (physicalResidueReconstruction root D base r stride v)) /
      (∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) L i) ≤
        ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
          (((1 + W) / L) ^ dim) ^ Fintype.card X) * M := by
  intro r target V hmass
  obtain ⟨hZ, hbound⟩ := hmass
  let volume := ∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) L i
  let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
    (((1 + W) / L) ^ dim) ^ Fintype.card X
  have hvolume : 0 < volume := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hH x) (hT x) hL i))
  have hfactor : 0 ≤ factor := mul_nonneg
    (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
    (pow_nonneg (pow_nonneg (div_nonneg (by linarith only [hW]) hL.le) _) _)
  have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root D residue H hH hrows hscaleLarge
    (fun v => f (translatePhysicalCube base v)) (fun v => hf _) hZ
  rw [referenceJetEnvelope_anisotropic_volume stride hs H T hL.ne' hscale] at hraw
  have hsum : (∑ v ∈ spatialWindow H 4, f (physicalResidueReconstruction root D base r stride v)) =
      ∑ v ∈ spatialWindow H 4, f (translatePhysicalCube base (physicalResidueReconstruction root D 0 r stride v)) := by
    apply Finset.sum_congr rfl
    intro v _
    exact congrArg f (physicalResidueReconstruction_translate root D base r stride v)
  apply (div_le_iff₀ hvolume).2
  rw [hsum]
  calc
    _ ≤ (factor * volume) * M := hraw.trans
      (mul_le_mul_of_nonneg_left hbound (mul_nonneg hfactor hvolume.le))
    _ = (factor * M) * volume := by ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_reference_jet_mass (m q : ℕ) :
    ∃ A T : ℕ, 2 ≤ A ∧ 2 ≤ T ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let root := allocatedPhysicalCubeRoot B U b S c x y
    let dirs := allocatedPhysicalCubeDirections B U b S x y
    let F := euclideanCoefficientJetMap U root dirs
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    ∃ f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ,
      Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) cap) ∧ Integrable f ξ ∧
      (∫ z, f z ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun z => density (cover z))).map F = realDensityMeasure ξ f ∧
      ∀ (_hm : (m : ℝ) ≤ P)
        (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
        (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
        (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
        (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
        (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
        (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P),
        (∀ {δ : ℝ} (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P),
        let Q := allocatedJetFourierBudget m q A P
        ∃ (Index : Type) (inst : Fintype Index), letI := inst
        ∃ (frequency : Index → ∀ j, (Fin q →₀ ℕ) → J j → ℤ) (coeff : Index → ℂ),
          (∀ a j e, e.degree ≤ j.val + 1 → ∀ t, |(frequency a j e t : ℝ)| ≤ Real.exp Q) ∧
          (∑ a, ‖coeff a‖) ≤ Real.exp Q ∧
          ∀ z : CoefficientTorus (K := Fin q) U,
            ‖(f (standardPhysicalJetMap U z) : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ δ) ∧
        ∀ {X : Type*} [Fintype X] [DecidableEq X]
          {Pmass : ℝ} (_hQ : allocatedJetFourierBudget m q A P ≤ Pmass)
          (_hX : (Fintype.card X : ℝ) ≤ Pmass)
          (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ Pmass)
          (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
          (hm : ∀ j e, coefficients (p j) e ∈ U j)
          (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
          {Rrank W τ ξ₀ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : ξ₀ ≤ 1) (_hρ : 0 < ρ)
          (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
          (_hsize : ∀ t, Real.exp ((Pmass + T) ^ T) ≤ (N t : ℝ))
          (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
          (_hRank : Real.exp ((Pmass + T) ^ T) ≤ Rrank)
          (_hspatial : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ))
          (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
          (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
            (2 * allocatedPhysicalEntryBudget B U b S c)) ≤ ρ)
          (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))
          (base : X → ℤ)
          (residue : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride),
          let H := trimmedSpatialRootScale τ N stride
          (∑ v ∈ spatialWindow H 4, f (physicalCubeEuclideanSample U d p hm
              (physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S c x y₀)
                (allocatedPhysicalCubeDirections B U b S x y₀) base
                (boundedColumnResidueRepresentative stride residue) stride v))) ≤
            (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
              (∏ t, ∏ _i : Unit ⊕ Fin q, H t) := by
  obtain ⟨A, hA, hdata⟩ := exists_allocated_jet_fourier_data m q
  obtain ⟨T, hT, hmass⟩ := exists_coarse_reference_jet_mass m q
  refine ⟨A, T, hA, hT, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod
  obtain ⟨d, hd, hdb, hdata⟩ := hdata B U b S c x hP hG hc hL hperiod
  refine ⟨d, hd, hdb, ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    density cap root dirs F cover ξ
  obtain ⟨f, hfc, hfb, hfi, hfm, hflaw, hfourier⟩ :=
    hdata y hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨f, hfc, hfb, hfi, hfm, hflaw, ?_⟩
  intro hm₀ hK hRP hσP hcount hI hn hJ hAP hCP hVP
  refine ⟨fun hδ hδP => hfourier hm₀ hK hRP hσP hcount hI hn hJ hAP hCP hVP hδ hδP, ?_⟩
  intro X _ _ Pmass hQ hX hdim p hp hm N stride hs Rrank W τ ξ₀ ρ hW hτ hξ hρ
    hτP hstride hsize hrank hRank hspatial hρ8 hρshift y₀ base residue H
  obtain ⟨Index, inst, frequency, coeff, hfreq, hcoeff, herr⟩ :=
    hfourier hm₀ hK hRP hσP hcount hI hn hJ hAP hCP hVP
      (show (0 : ℝ) < 1 by norm_num) (by simpa using Real.one_le_exp hP)
  let _ := inst
  have hPmass := (allocatedJetFourierBudget_nonneg m q A hP).trans hQ
  have hN (t : X) : 0 < N t := by
    exact_mod_cast (Real.exp_pos _).trans_le (hsize t)
  have hgeometry := allocatedNarrow_reference_jet_geometry B U b S c x y₀ N stride hN hs
    hW hτ hξ hρ hspatial hρ8 hρshift
  have hcoverP : (d : ℝ) ≤ Real.exp Pmass :=
    hdb.trans (Real.exp_le_exp.mpr ((allocatedJetFourierBudget_dominates m q A hP).1.trans hQ))
  exact hmass hPmass hX hdim U ν frequency
    (fun a j e he t => (hfreq a j e he t).trans (Real.exp_le_exp.mpr hQ)) coeff
    (hcoeff.trans (Real.exp_le_exp.mpr hQ)) p hp hm d hd hcoverP stride hs hτ hτP
    hstride (fun t => (N t : ℝ)) hsize hrank hRank
    (allocatedPhysicalCubeRoot B U b S c x y₀) (allocatedPhysicalCubeDirections B U b S x y₀)
    base residue H (fun t => (hgeometry t).1) (fun t => (hgeometry t).2.1)
    (fun t => (hgeometry t).2.2.1) (fun t => (hgeometry t).2.2.2)
    f (fun z => (hfb z).1) hfi hfm herr

end Erdos3.VectorPolynomial

end

end OAI
