import OAI.Combinatorics.Progressions.Fourier.AllocatedIdealCoefficientFourier
import OAI.Combinatorics.Progressions.Probability.AllocatedErrorSampledMass
import OAI.Combinatorics.Progressions.Probability.AllocatedIdealCoefficientMass
import OAI.Combinatorics.Progressions.Probability.AllocatedMassTupleComparison

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_weighted_error_tail (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {Ksp : Type*} [Fintype Ksp]
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
    (N : X → ℝ) (_hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ N x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) N R (U j) (p j))
    (_hR : Real.exp ((P + K) ^ K) ≤ R)
    (root : Ksp → ℤ) (D : Matrix (Fin q) Ksp ℤ) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option Ksp) X stride))
    (W₀ : Option Ksp × X → ℝ) (_hW₀ : ∀ z, 0 < W₀ z)
    (_hZ₀ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W₀ z)
    (H T : X → ℝ) (_hH : ∀ x, 0 < H x) (_hT : ∀ x, 0 < T x)
    {Wsp Lsp : ℝ} (_hLsp : 0 < Lsp) (_hsc : ∀ x, H x = (1 + Wsp) * T x)
    (_hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (_hwidth : ∀ x, ρ * N x ≤ 20 * (stride x : ℝ) * H x)
    (_hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (ψ : (X → (Unit ⊕ Fin q) → ℤ) → ℂ) {Cψ : ℝ} (_hCψ : 0 ≤ Cψ)
    (_hψ : ∀ w ∈ spatialWindow H 4, ‖ψ w‖ ≤ Cψ)
    (test : (X → (Unit ⊕ Fin q) → ℤ) → ℂ) (_htest : ∀ w, ‖test w‖ ≤ 1)
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR₀ : ∀ j, 0 < R₀ j) (hσ : ∀ j, 0 < σ j)
    {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
      (allocatedPrincipalSides B U b S))
    (rows : ∀ j : Fin m, BoundedBooleanJet (Fin q) (j.val + 1) → Finset α)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (period : ℕ) [NeZero period]
    (_hperiod : ∀ j, integerScalarLattice (BoundedBooleanJet (Fin q) (j.val + 1)) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (η : ℝ≥0) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ L : ℝ} (_hδ : 0 < δ) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J) : ℝ) ≤ L)
    (_hδL : δ⁻¹ ≤ Real.exp L),
    let O := fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)
    let A := Real.toNNReal (coefficientDeckPeriodCap O Q period)
    (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedErrorKernelCap B U b S (O := O) η A V ≤ Real.exp P →
    let error := restrictedChartDensity (mixedCoveredJetChart U o b hb bW d)
      (mixedCoveredJetRegion (O := O) (E := Q) U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)))
      1 (fun z : MixedCoveredJetSource I O Q n d =>
        allocatedCoveredFixedFactor B U b hR₀ hσ S x u v rows Q d z.1 z.2 *
          ((η : ℝ) / (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)))
    let M := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (((1 + Wsp) / Lsp) ^ q) ^ Fintype.card X
    let scale := ∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) Lsp i
    let window := spatialWindow H 4
    let reconstruct := fun a : cells => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative stride a.val) stride
    (∑ t : cells × window,
      ‖(selectedResidueCellWeight stride cells W₀ t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val)‖ *
          error (physicalCubeEuclideanSample U d p hm (reconstruct t.1 t.2.val))) ≤
      Cψ * (volumeFactor * (M + 2 * δ + ε)) := by
  obtain ⟨K, hK, hsample⟩ := exists_allocated_error_sampled_mass m q
  refine ⟨K, hK, ?_⟩
  intro X _ _ Ksp _ J _ P hP hn hdim U _ _ _ μ _ _ ν _ _ p hp hm d _ stride hs R S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride N hsize hrank hR root D base cells W₀ hW₀ hZ₀
    H T hH hT Wsp Lsp hLsp hsc hrows hwidth hprofile ψ Cψ hCψ hψ test htest
    G _ I _ n B _ b R₀ σ S o hR₀ hσ α _ x u v rows _ hb Q _ bW period _ hperiod
    η C V hC hV δ L hδ hL hamb hδL O A hLip hfreqP hcoeffP error M volumeFactor scale window reconstruct
  let g := allocatedCoefficientErrorMajorant B U b S o hR₀ hσ x u v rows η A d
  let p₀ := fun j => translate (fun x => (base x : ℝ)) (p j)
  have hp₀ (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (p₀ j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hm₀ (j e) : coefficients (p₀ j) e ∈ U j :=
    coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j) e
  have hrank₀ (j) : HasLayerSamplingRank (j.val + 1) N R (U j) (p₀ j) :=
    (hasLayerSamplingRank_translate_iff _ _ N R (U j) (p j) (hp j)).mpr (hrank j)
  let V₁ := referenceJetEnvelopeWidths (q := q) stride H
  have hV₁ := referenceJetEnvelopeWidths_pos (q := q) stride hs H hH
  have hg0 (y) : 0 ≤ g y :=
    ((allocatedErrorTorusKernel_bounds B U b S o hR₀ hσ x u v rows η A C V hC hV).1
      (coveredJetAmbientTorus U d y)).1
  have hscale : 0 < scale := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin q) (hH x) (hT x) hLsp i))
  have hmass (a : cells) :
      (∑ w ∈ window, g (physicalCubeEuclideanSample U d p hm (reconstruct a w))) ≤
        (volumeFactor * (M + 2 * δ + ε)) * scale := by
    let r := boundedColumnResidueRepresentative stride a.val
    let target := columnResiduePattern stride
      (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 r))
    obtain ⟨hZ, hmean, _⟩ := hsample hP hn hdim U μ ν p₀ hp₀ hm₀ d stride hs
      hS hSP hρ hε hρP hεP hstride N hsize hrank₀ hR
      {target} (Finset.singleton_nonempty _) V₁ hV₁ (fun z => hwidth z.2)
      B b S o hR₀ hσ x u v rows hb bW period hperiod η C V hC hV hδ hL hamb hδL
      hLip hfreqP hcoeffP
    let f := fun w => g (physicalCubeEuclideanSample U d p₀ hm₀ w)
    have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root D a.val
      H hH hrows hprofile f (fun _ => hg0 _) hZ
    have hvol : ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V₁ i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) = volumeFactor * scale :=
      referenceJetEnvelope_anisotropic_volume stride hs H T hLsp.ne' hsc
    have hvol0 : 0 ≤ (3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V₁ i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) := by
      exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (Finset.prod_nonneg (fun i _ => (residueProfileWidth_pos stride V₁ hs hV₁ i).le)))
        (pow_pos smoothProbabilityProfile_pos_zero _).le
    have hfinal := hraw.trans (mul_le_mul_of_nonneg_left hmean hvol0)
    rw [hvol] at hfinal
    dsimp only [f, p₀] at hfinal
    simp_rw [physicalCubeEuclideanSample_translate U d p hm base,
      ← physicalResidueReconstruction_translate root D base] at hfinal
    change (∑ w ∈ window, g (physicalCubeEuclideanSample U d p hm (reconstruct a w))) ≤
      (volumeFactor * scale) * (M + 2 * δ + ε) at hfinal
    exact hfinal.trans_eq (by ring)
  have hdom (y) : error y ≤ g y :=
    allocatedCoefficientError_le_majorant B U b S o hR₀ hσ x u v rows hb bW d period hperiod η C V hC hV y
  calc
    _ ≤ ∑ t : cells × window,
        ‖(selectedResidueCellWeight stride cells W₀ t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
          test (reconstruct t.1 t.2.val)‖ *
            g (physicalCubeEuclideanSample U d p hm (reconstruct t.1 t.2.val)) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hdom _) (norm_nonneg _))
    _ ≤ _ := selectedResidue_coefficient_tail_of_window_mass stride cells W₀ hW₀ hZ₀ window ψ
      (fun a w => test (reconstruct a w))
      (fun a w => g (physicalCubeEuclideanSample U d p hm (reconstruct a w)))
      hscale hCψ hψ (fun a w => htest _) (fun a w => hg0 _) hmass

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z η : ℝ)

def allocatedRefinedReferenceTailBound (Etail : ℝ) : Prop :=
    let coefficientScale := ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
    let chart := mixedCoveredJetChart U o b hb bW d
    let region := mixedCoveredJetRegion (O := O) (E := Kcov) U o b d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x (fun a => (0 : ℤ) + (x a none : ℤ))
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
    let f := canonicalSpatialSiteDensity selection (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun u r (v : X → (Unit ⊕ (Fin dim)) → ℤ) => ∏ t,
      spatialSiteApprox (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix
            (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u (reference u r))) modulus)))
        modulus f (H t) 4 mesh (v t)
    let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let window := spatialWindow H 4
    let F := fun u r (a : cells) => physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r))) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r))) base
      (boundedColumnResidueRepresentative q a.val) q
    let factor := fun u r (t : cells × window) =>
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ u r t.2.val / (A : ℂ)) * test (F u r t.1 t.2.val)
    let error := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 * (η/coefficientScale))
    ∀ u r, (∑ t : cells × window, ‖factor u r t‖ * error u r (point (F u r t.1 t.2.val))) ≤ Etail

def allocatedRefinedTupleScalarEstimate (Etail : ℝ) : Prop :=
    let coefficientScale := ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
    let chart := mixedCoveredJetChart U o b hb bW d
    let region := mixedCoveredJetRegion (O := O) (E := Kcov) U o b d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x (fun a => (0 : ℤ) + (x a none : ℤ))
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
    let f := canonicalSpatialSiteDensity selection (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun u r (v : X → (Unit ⊕ (Fin dim)) → ℤ) => ∏ t,
      spatialSiteApprox (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix
            (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u (reference u r))) modulus)))
        modulus f (H t) 4 mesh (v t)
    let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let E₀ := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M (1/(M : ℝ)) C₀ ρ ξ
    let Γ := (modulus : ℝ)^Fintype.card (Unit ⊕ (Fin dim))
    let E₁ := E₀ + Γ*(anisotropicSpatialDensityLip selection (1/(M : ℝ))*(1+W))*δ
    let Esite := Fintype.card X*(E₁ + 4*Γ*(anisotropicSpatialDensityLip selection (1/(M : ℝ))*(1+W))*mesh)*
      (1 + Γ*anisotropicSpatialDensityCap selection (1/(M : ℝ)) + E₁)^Fintype.card X
    let window := spatialWindow H 4
    let F := fun u r (a : cells) => physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r))) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r))) base
      (boundedColumnResidueRepresentative q a.val) q
    let factor := fun u r (t : cells × window) =>
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ u r t.2.val / (A : ℂ)) * test (F u r t.1 t.2.val)
    let proxy := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r) (fun a => coefficientJetAxisEquiv O I n z.1 a.val) / coefficientScale))
    let source := fun y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides =>
      ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (g y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
    let target := fun u r => ∑ t : cells × window,
      factor u r t * (proxy u r (point (F u r t.1 t.2.val)) : ℂ)
    ‖(whole).complexMean source / (Z : ℂ) -
      ((frozen).complexMean (fun u => ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).complexMean (target u))) /
        (Z : ℂ)‖ ≤
      Cg*(24*(probabilityProfileLipschitz : ℝ)*Fintype.card (Option (LayerSamplerVariables G I n B) × X)/ρ)/Z +
        Esite * coarseReferenceMassConstant dim X W S.value / Z + Etail / Z

omit [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
  [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedRefinedTupleMassEstimate_scalar {Etail : ℝ} (hZ : 0 < Z)
    (hestimate : allocatedRefinedTupleMassEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass point test Cg Z η)
    (htail : allocatedRefinedReferenceTailBound (τ := τ) (ξ := ξ) B U b hR hσ S x rows X hM selection hx modulus
      q reference hb o bW d N hW mesh base cells point test η Etail) :
    allocatedRefinedTupleScalarEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass point test Cg Z Etail := by
  unfold allocatedRefinedTupleMassEstimate at hestimate
  unfold allocatedRefinedTupleScalarEstimate
  dsimp only at hestimate ⊢
  refine hestimate.trans ?_
  refine ((frozen).mean_mono (g := fun _ => _) (fun u => ?_)).trans_eq ((frozen).mean_const _)
  refine (((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).mean_mono
    (g := fun _ => _) (fun r => ?_)).trans_eq
      (((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).mean_const _)
  exact add_le_add le_rfl (div_le_div_of_nonneg_right (htail u r) hZ.le)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_reference_tail_bound :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (modulus : ℕ) [NeZero modulus]
    (_hspatialPeriod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    {mesh : ℝ} (_hmesh : 0 < mesh) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ z, ‖test z‖ ≤ 1)
    {P Rrank ε : ℝ} (_hP : 0 ≤ P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (_hτP : 1 / τ ≤ Real.exp P) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp P)
    (_hsize : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((P + K) ^ K) ≤ Rrank)
    (η : ℝ≥0) {δf L : ℝ} (_hδf : 0 < δf) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ L) (_hδL : δf⁻¹ ≤ Real.exp L),
    let A := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus)
    (allocatedErrorKernelLip B U b S (O := jets) η A C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedErrorKernelCap B U b S (O := jets) η A V ≤ Real.exp P →
    let Cψ := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    let Merr := (η : ℝ) * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)
    allocatedRefinedReferenceTailBound (τ := τ) (ξ := ξ) B U b hR hσ S x jetRows X hM selection hx modulus
      q reference hb o bW d N hW mesh base cells (physicalCubeEuclideanSample U d p hm) test η
        (Cψ * (Vsp * (Merr + 2 * δf + ε))) := by
  obtain ⟨K, hK, htail⟩ := exists_allocated_weighted_error_tail m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V hC hV ν _ _
    M hM selection hx modulus _ hspatialPeriod hperiod X _ _ q hq reference N hN
    W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget mesh hmesh base cells hmass
    p hp hm test htest P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    η δf L hδf hL hamb hδL A hLip hfreqP hcoeffP Cψ Vsp Merr
  let _ := coefficientTorus_compact_of_lattice (K := Fin dim) U
  let _ : MeasurableSpace (CoefficientTorus (K := Fin dim) U) := borel _
  let _ : BorelSpace (CoefficientTorus (K := Fin dim) U) := ⟨rfl⟩
  unfold allocatedRefinedReferenceTailBound
  intro coefficientScale chart region H T Vs hpivot f ψ scale window F factor error u r
  let y := principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u (reference u r)
  have hgeo (t : X) := allocatedNarrow_reference_jet_geometry B U b S (fun _ => 0) x y N q hN hq
    hW hτ hξ1 hρ hsizeSp hρ8 hρshift t
  have hH (t) : 0 < H t := (hgeo t).1
  have hT (t) : 0 < T t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2
  have hCψ : 0 ≤ Cψ := pow_nonneg (mul_nonneg (by positivity)
    (anisotropicSpatialDensityCap_nonneg selection (by positivity))) _
  have hψ (w) (hw : w ∈ window) : ‖ψ u r w‖ ≤ Cψ :=
    allocatedReferenceSpatialProxy_bound B U b S x y hM selection hx modulus hspatialPeriod H hH hW hbudget hmesh w hw
  have h := htail hP hX hdim U (probabilityAddHaar _) ν p hp hm d q hq
    (Real.exp_pos P).le le_rfl hτ hε hτP hεP hstride (fun t => (N t : ℝ)) hsize hrank hRank
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) (allocatedPhysicalCubeDirections B U b S x y)
    base cells Vs (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass H T hH hT
    (Nat.cast_pos.mpr S.positive) (trimmedSpatial_scale_ratio hW N q)
    (fun t => (hgeo t).2.1) (fun t => (hgeo t).2.2.1) (fun t => (hgeo t).2.2.2)
    (ψ u r) hCψ hψ test htest B b S o hR hσ x u (reference u r) jetRows hb bW modulus hperiod
    η C V hC hV hδf hL hamb hδL hLip hfreqP hcoeffP
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z η : ℝ)

omit [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
  [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedRefinedTupleScalarEstimate_mono {Ea Eb : ℝ} (hZ : 0 ≤ Z)
    (hestimate : allocatedRefinedTupleScalarEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass point test Cg Z Ea)
    (herror : Ea ≤ Eb) :
    allocatedRefinedTupleScalarEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass point test Cg Z Eb := by
  unfold allocatedRefinedTupleScalarEstimate at hestimate ⊢
  dsimp only at hestimate ⊢
  exact hestimate.trans (add_le_add le_rfl (div_le_div_of_nonneg_right herror hZ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

def AllocatedIdealReferenceTailAt (K : ℕ) : Prop :=
    ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (modulus : ℕ) [NeZero modulus]
    (_hspatialPeriod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    {mesh : ℝ} (_hmesh : 0 < mesh) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ z, ‖test z‖ ≤ 1)
    {D Psp pNum E e w lengthLog Rrank : ℝ}
    (_hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (_hPsp : 0 ≤ Psp) (_hpNum : 0 ≤ pNum) (_hE : 0 ≤ E)
    (_he : 0 ≤ e) (_hw : 0 ≤ w) (_hlengthLog : 0 ≤ lengthLog)
    (_hmPsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp) (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (_hX : (Fintype.card X : ℝ) ≤ pNum)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ pNum)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (_hτP : 1 / τ ≤ Real.exp pNum) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp pNum)
    (_herrorNum : profileReferenceErrorLog Psp E ≤ pNum)
    (_hmodulus : modulus ≤ M ^ (m + 1)) (_hMP : (M : ℝ) ≤ Real.exp Psp)
    (_hS : (S.value : ℝ) ≤ Real.exp lengthLog)
    {Dsp : ℝ} (_hDsp : Dsp ≤ Real.exp Psp) (_hWscale : W ≤ Dsp * (S.value : ℝ)),
    let gainLog := allocatedProfileGainLog m D Psp w
    let input := allocatedActualProfileInput m D pNum e gainLog lengthLog
    let Pout := allocatedProfileFourierOutput input
    (∀ t, Real.exp ((Pout + K) ^ K) ≤ (N t : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j)) →
    Real.exp ((Pout + K) ^ K) ≤ Rrank →
    ∀ Z : ℝ, 1 / 2 ≤ Z →
    allocatedRefinedReferenceTailBound (τ := τ) (ξ := ξ) B U b hR hσ S x jetRows X hM selection hx modulus
      q reference hb o bW d N hW mesh base cells (physicalCubeEuclideanSample U d p hm) test
      (physicalIdealErrorShare (allocatedReferenceIdealError m D Psp E) (allocatedIdealVolumeEnvelope m D pNum))
      (Z * Real.exp (-E))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_ideal_reference_tail (m dim : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ AllocatedIdealReferenceTailAt m dim K := by
  obtain ⟨K, hK, htail⟩ := exists_allocated_reference_tail_bound m dim
  refine ⟨K, hK, ?_⟩
  unfold AllocatedIdealReferenceTailAt
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V hC hV ν _ _
    M hM selection hx modulus _ hspatialPeriod hperiod X _ _ q hq reference N hN
    W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget mesh hmesh base cells hmass
    p hp hm test htest D Psp pNum E e w lengthLog Rrank hd hPsp hpNum hE he hw hlengthLog
    hmPsp hdimPsp hGPsp hXPsp hX hdim hCP hVP hτP hstride herrorNum hmodulus hMP hS
    Dsp hDsp hWscale gainLog input Pout hsize hrank hRank Z hZ
  let jets := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
  let accuracy := profileReferenceAccuracy Psp E
  have hacc := profileReferenceAccuracy_bounds hPsp hE
  have haccInv : accuracy⁻¹ ≤ Real.exp pNum := hacc.2.2.le.trans (Real.exp_le_exp.mpr herrorNum)
  have hJQ := allocatedProfile_dimensions U b o B hd hb bW
  have hgain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hd.nonneg hPsp hw
  have herror := allocatedReferenceIdealError_nonneg m hd.nonneg hPsp hE
  have hvolume : 0 ≤ allocatedIdealVolumeEnvelope m D pNum := by
    have hs := allocatedSupportEnvelope_nonneg m hd.nonneg hpNum
    unfold allocatedIdealVolumeEnvelope
    exact mul_nonneg hd.nonneg (by linarith)
  let η : ℝ≥0 := ⟨physicalIdealErrorShare (allocatedReferenceIdealError m D Psp E)
    (allocatedIdealVolumeEnvelope m D pNum), (physicalIdealErrorShare_pos _ _).le⟩
  have hη : η ≤ 1 := physicalIdealErrorShare_le_one herror hvolume
  let A := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus)
  have hA : (A : ℝ) ≤ Real.exp gainLog := by
    have h := allocatedProfileGain_le_exp B hd hJQ.2 M modulus hmodulus 1 hPsp hw
      hMP (Real.one_le_exp hw)
    simpa only [one_pow, mul_one] using h
  obtain ⟨hL, hpOut, hamb, hδL, hLip, hfreq, hcoeff⟩ :=
    allocatedIdealCoefficient_fourier_budget B hd U b S hpNum he hgain hlengthLog hJQ.1
      η A hη hA hS C V hCP hVP haccInv
  have hPout : 0 ≤ Pout := hpNum.trans hpOut
  have hraw := htail B U b hR hσ S x hb o bW d C V hC hV ν hM selection hx modulus
    hspatialPeriod hperiod q hq reference N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget
    hmesh base cells hmass p hp hm test htest hPout (hX.trans hpOut) (hdim.trans hpOut)
    (hτP.trans (Real.exp_le_exp.mpr hpOut))
    (fun t => (hstride t).trans (Real.exp_le_exp.mpr hpOut)) hacc.1
    (by simpa only [one_div] using haccInv.trans (Real.exp_le_exp.mpr hpOut))
    hsize hrank hRank η hacc.1 hL hamb hδL hLip hfreq hcoeff
  let Cψ := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
    anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
  let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
    (((1 + W) / S.value) ^ dim) ^ Fintype.card X
  let Merr := (η : ℝ) * A *
    (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
      Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)
  have hMerr : Merr ≤ accuracy := by
    dsimp only [Merr, A]
    rw [Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg jets Q modulus)]
    exact allocatedIdealCoefficientMass_bound B hd J Q C hpNum hPsp hJQ.1 hJQ.2 hCP
      M modulus hmodulus hMP
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast (Nat.succ_le_iff.mpr S.positive)
  have hper := coefficientErrorPeriod_exp_sq hPsp hmPsp hMP hmodulus
  have hspatial := coefficientErrorSpatialFactor_exp_bound dim X selection hPsp hM hMP hper
    hdimPsp hGPsp hXPsp hS1 hW hDsp hWscale
  have hsmall : (Cψ * (Vsp * (Merr + 2 * accuracy + accuracy))) / Z ≤ Real.exp (-E) := by
    simpa only [Cψ, Vsp, mul_assoc] using profileReferenceAccuracy_normalized_error
      hspatial.1 hspatial.2 hMerr (le_refl accuracy) (le_refl accuracy) hZ
  have hZpos : 0 < Z := by linarith
  have htotal : Cψ * (Vsp * (Merr + 2 * accuracy + accuracy)) ≤ Z * Real.exp (-E) := by
    simpa only [mul_comm] using (div_le_iff₀ hZpos).mp hsmall
  dsimp only [allocatedRefinedReferenceTailBound] at hraw ⊢
  intro u r
  exact (hraw u r).trans htotal

end Erdos3.VectorPolynomial

end

end OAI
