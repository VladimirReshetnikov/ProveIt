import OAI.Combinatorics.Progressions.Estimates.AllocatedActivePlateauAverage
import OAI.Combinatorics.Progressions.Estimates.AllocatedMaskedProfileCap
import OAI.Combinatorics.Progressions.Fourier.AllocatedProbabilityFourier
import OAI.Combinatorics.Progressions.Sampling.AllocatedGridlessWindowMajorant

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem allocatedProbabilityMajorant_sample {m q : ℕ} {G X : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (laws : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      PMF (CoefficientJetAxisRow (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) a.val))
    (η A : ℝ≥0) (d : ℕ) [NeZero d]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : X → (Unit ⊕ Fin q) → ℤ) :
    allocatedProbabilityMajorant B U b S o laws η A d
        (physicalCubeEuclideanSample U d p hm z) =
      allocatedProbabilityMajorant B U b S o laws η A 1
        (physicalCubeEuclideanSample U 1 p hm z) := by
  unfold allocatedProbabilityMajorant
  rw [coveredJetAmbientTorus_sample]

theorem exists_allocated_probability_sampled_mass (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d]
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin q)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin q) × X → ℝ) (_hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (laws : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      PMF (CoefficientJetAxisRow (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) a.val))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (_hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (_bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (η A : ℝ≥0) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ L : ℝ} (_hδ : 0 < δ) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J) : ℝ) ≤ L)
    (_hδL : δ⁻¹ ≤ Real.exp L),
    let O := fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)
    (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedErrorKernelCap B U b S (O := O) η A V ≤ Real.exp P →
    let g := allocatedProbabilityMajorant B U b S o laws η A d
    let M := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => g (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))) ≤ M + 2 * δ + ε := by
  obtain ⟨K, hK, htest⟩ := exists_physical_jet_integral_comparison m q
  refine ⟨K, hK, ?_⟩
  intro X _ _ J _ P hP hn hdim U _ _ _ μ _ _ ν _ _ p hp hm d _ stride hs R S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth
    G _ I _ n B _ b R₀ σ S o laws _ hb Q _ bW
    η A C V hC hV δ L hδ hL hamb hδL O hLip hfreqP hcoeffP g M
  obtain ⟨F, inst, frequency, c, _hcard, hfreq, hsum, happrox⟩ :=
    exists_allocated_probability_standard_fourier B U b S o laws 1 η A C V
      hC hV hδ hL hamb hLip hδL
  let _ := inst
  simp only [Nat.cast_one, mul_one] at hfreq
  let g₁ := allocatedProbabilityMajorant B U b S o laws η A 1
  have hmass := allocatedProbabilityMajorant_integrable_mass B U b S o laws
    hb bW 1 ν η A C V hC hV
  obtain ⟨hZ, hclose⟩ := htest hP hn hdim U μ ν (by positivity) hfreqP frequency hfreq c
    (by positivity) hcoeffP hsum p hp hm 1 Nat.zero_lt_one (by simpa only [Nat.cast_one] using Real.one_le_exp hP) stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth g₁ hmass.1 hδ.le happrox
  have hbound : selectedResidueDensityMass stride cells W
      (fun z => g (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))) ≤ M + 2 * δ + ε := by
    have he := (abs_le.mp hclose).2
    have hm' : (∫ y, g₁ y ∂(Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))) ≤ M := hmass.2
    dsimp only [g]
    simp_rw [allocatedProbabilityMajorant_sample B U b S o laws η A d p hm]
    change selectedResidueDensityMass stride cells W
      (fun z => g₁ (physicalCubeEuclideanSample U 1 p hm (standardPhysicalCubeOutput z))) ≤ _
    linarith
  exact ⟨hZ, hbound⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop) [DecidablePred selected]
variable (W : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, Finset (CoefficientJetAxisRow O a.val))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
variable [NeZero q]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "density" => allocatedSupportedGridJetDensity B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "weight" => allocatedGridWindowWeight B U b S O selected W laws
local notation "χ" => allocatedChartGridMultiplier B U b S O hb o bW d weight
local notation "profile" => allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f
local notation "residue" => fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q

variable (CM Cf : ℝ≥0) (hCM : 1 ≤ (CM : ℝ)) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x rows j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)

local notation "amplitude" => Real.toNNReal (coefficientDeckPeriodCap O Q q) *
  CM ^ Fintype.card (LayerSamplerAxis I n) * Cf

include hCM hfb hm in
theorem allocatedSelectedConditionalError_le_probability_majorant
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (g : ((a : {a : {a // grid a} // selected a}) →
      CoefficientJetAxisRow O (Subtype.val (Subtype.val a))) → ℂ)
    {N ε : ℝ} (hN : 0 < N) (hε : 0 ≤ ε)
    (hzero : ∀ z : ((a : {a : {a // grid a} // selected a}) →
      CoefficientJetAxisRow O (Subtype.val (Subtype.val a))), (∃ a, z a ∉ W a.val) →
        (∏ a, (laws a.val (z a)).toReal) = 0 ∧ g z = 0)
    (he : ∀ z : ((a : {a : {a // grid a} // selected a}) →
      CoefficientJetAxisRow O (Subtype.val (Subtype.val a))),
        ‖(N : ℂ) * ((∏ a, (laws a.val (z a)).toReal : ℝ) : ℂ) - g z‖ ≤ ε)
    (hW : ∀ a, selected a → (W a).Nonempty) (δ : ℝ≥0)
    (hbudget : (ε / N) * (∏ a : {a // grid a}, if selected a then ((W a).card : ℝ) else 1) ≤ δ)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (y : EuclideanJetLayers U O) :
    ‖allocatedSelectedConditionalError B U b hR hσ S x rows hb o bW d q y₀ hcell
      selected f g N y‖ ≤ allocatedProbabilityMajorant B U b S o
        (allocatedGridWindowPMF B U b S O selected W laws hW) δ amplitude d y := by
  let E := ε / N
  let gfull := allocatedSelectedGridExtension B U b hR hσ S x rows q
    (principalResidueLabel q y₀) hcell selected g N
  let a := allocatedChartGridMultiplier B U b S O hb o bW d density
  let c := allocatedComplexGridMultiplier B U b S O hb o bW d gfull
  let D : EuclideanJetLayers U O → ℂ := fun z =>
    ((a z * profile z : ℝ) : ℂ) - c z * (profile z : ℂ)
  have herror := allocatedSelectedGridExtension_error B U b hR hσ S x rows q
    (principalResidueLabel q y₀) hcell selected W g hN hzero he
  have hF := allocatedLongProfileDensity_period_bound (Q := Q) B U b S x rows q (residue)
    (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)
    d q hperiod CM Cf hCM hm f hfb
  have hmajor : E * |χ y * profile y| ≤ allocatedProbabilityMajorant B U b S o
      (allocatedGridWindowPMF B U b S O selected W laws hW) δ amplitude d y := by
    simpa only [allocatedWholeMaskedGridlessProfile] using
      (allocatedGridlessWindow_le_probability_majorant B U b S x
        (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)
        rows hb o bW d selected W laws hW
        (allocatedLongProfileDensity B U b S x rows q (residue) f)
        E (div_nonneg hε hN.le) δ amplitude hbudget hF C V hC hV y)
  simp only [allocatedSelectedConditionalError,
    allocatedWholeMaskedCoveredProfile_conditional_mean B U b hR hσ S x rows hb o bW d
      q y₀ hcell hperiod f]
  change ‖D y‖ ≤ _
  have hχ : 0 ≤ χ y := allocatedChartGridMultiplier_nonneg B U b S O hb o bW d weight
    (allocatedGridWindowWeight_nonneg B U b S O selected W laws) y
  have heq : D y = ((a y : ℂ) - c y) * (profile y : ℂ) := by
    dsimp only [D]
    push_cast
    ring
  calc
    ‖D y‖ = ‖(a y : ℂ) - c y‖ * |profile y| := by
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (E * χ y) * |profile y| := mul_le_mul_of_nonneg_right
      (allocatedGridMultiplier_error B U b S O hb o bW d density gfull weight E herror y)
      (abs_nonneg _)
    _ = E * |χ y * profile y| := by rw [abs_mul, abs_of_nonneg hχ]; ring
    _ ≤ _ := hmajor

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_conditional_sampled_error (m dim : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d]
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (_hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR₀ : ∀ j, 0 < R₀ j) (hσ : ∀ j, 0 < σ j)
    [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (modulus : ℕ) [NeZero modulus]
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel modulus y = principalResidueLabel modulus y₀)))
    (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop) [DecidablePred selected]
    (windows : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, Finset (CoefficientJetAxisRow (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) a.val))
    (_hwindows : ∀ a, selected a → (windows a).Nonempty)
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, BoundedBooleanJet (Fin dim) (a.val.1.val + 1)) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))) j modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
        (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))) j
        (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) modulus) z ∧
      allocatedIntegerKernelMask B U b S x (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))) j modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
        (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))) j
        (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) modulus) z ≤ CM)
    (approx : ((a : {a : {a // allocatedGridAxis (I := I) U b S.value a} // selected a}) →
      CoefficientJetAxisRow (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) a.val.val) → ℂ)
    {N εgrid : ℝ} (_hN : 0 < N) (_hεgrid : 0 ≤ εgrid)
    (_hzero : ∀ z : ((a : {a : {a // allocatedGridAxis (I := I) U b S.value a} // selected a}) →
      CoefficientJetAxisRow (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) a.val.val), (∃ a, z a ∉ windows a.val) →
        (∏ a, (allocatedSupportedGridJetPMF B U b hR₀ hσ S x (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))) modulus (principalResidueLabel modulus y₀) hcell a.val (z a)).toReal) = 0 ∧ approx z = 0)
    (_hpoint : ∀ z : ((a : {a : {a // allocatedGridAxis (I := I) U b S.value a} // selected a}) →
      CoefficientJetAxisRow (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) a.val.val),
        ‖(N : ℂ) * ((∏ a, (allocatedSupportedGridJetPMF B U b hR₀ hσ S x (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))) modulus (principalResidueLabel modulus y₀) hcell a.val (z a)).toReal : ℝ) : ℂ) - approx z‖ ≤ εgrid)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (_hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) ((fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))) j)).mulVecLin.range)
    (η : ℝ≥0)
    (_hbudget : (εgrid / N) * (∏ a : {a // allocatedGridAxis (I := I) U b S.value a},
      if selected a then ((windows a).card : ℝ) else 1) ≤ η)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ L : ℝ} (_hδ : 0 < δ) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) J) : ℝ) ≤ L)
    (_hδL : δ⁻¹ ≤ Real.exp L),
    let O := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
    let A := Real.toNNReal (coefficientDeckPeriodCap O Q modulus) * CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedErrorKernelCap B U b S (O := O) η A V ≤ Real.exp P →
    let error := allocatedSelectedConditionalError B U b hR₀ hσ S x (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
      hb o bW d modulus y₀ hcell selected f approx N
    let M := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))‖) ≤ M + 2 * δ + ε := by
  obtain ⟨K, hK, htest⟩ := exists_allocated_probability_sampled_mass m dim
  refine ⟨K, hK, ?_⟩
  intro X _ _ J _ P hP hn hdim U _ _ _ μ _ _ ν _ _ p hp hm d _ stride hs R S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth
    G _ I _ n B _ b R₀ σ S o hR₀ hσ _ _ x modulus _ y₀ hcell selected _ windows hwindows
    f CM Cf hCM hfb hmask approx N εgrid hN hεgrid hzero hpoint _ hb Q _ bW
    hperiod η hbudget C V hC hV δ L hδ hL hamb hδL O A hLip hfreqP hcoeffP error M
  let laws := allocatedSupportedGridJetPMF B U b hR₀ hσ S x (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim))) modulus (principalResidueLabel modulus y₀) hcell
  let aux := allocatedGridWindowPMF B U b S O selected windows laws hwindows
  have herror := allocatedSelectedConditionalError_le_probability_majorant B U b hR₀ hσ S x (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
    hb o bW d modulus y₀ hcell selected windows f CM Cf hCM hfb hmask hperiod
    approx hN hεgrid hzero hpoint hwindows η hbudget C V hC hV
  obtain ⟨hZ, hbound⟩ := htest hP hn hdim U μ ν p hp hm d stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells W hW hwidth
    B b S o aux hb bW η A C V hC hV hδ hL hamb hδL hLip hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  exact (selectedResidueDensityMass_mono stride cells W hW hZ
    (fun z => herror (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z)))).trans hbound

end Erdos3.BooleanCubeKernel

end

end OAI
