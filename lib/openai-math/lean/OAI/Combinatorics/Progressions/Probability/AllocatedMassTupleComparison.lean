import OAI.Combinatorics.Progressions.Linear.AllocatedGoodKernelSpatialDensity
import OAI.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "whole" => principalTupleWeights B (layerSamplerDegree I n) sides
  (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := α) B U b S
local notation "long" => allocatedLongTupleWeights (α := α) B U b S

variable (period : ℕ) [NeZero period] (hp : 0 < period)
variable (hsize : ∀ t, (Fintype.card α + 1) * period ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S) t)
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable (f : X → PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S) → ℂ)
variable (hf : ∀ y, Integrable (fun p => f p y) μ)

include hf

theorem allocatedTuple_integral_residues :
    (∫ p, (whole).complexMean (f p) ∂μ) =
      (frozen).complexMean (fun u => ((long).fiberLaw (principalResidueLabel period)).complexMean
        (fun r => ∫ p, (allocatedLongResidueWeights B U b S period hp r hsize).complexMean
          (fun v => f p (principalAxisJoin grid u v)) ∂μ)) := by
  have hi (u) (r) := (allocatedLongResidueWeights B U b S period hp r hsize).complexMean_integrable
    μ (fun p v => f p (principalAxisJoin grid u v)) (fun v => hf (principalAxisJoin grid u v))
  calc
    _ = ∫ p, (frozen).complexMean (fun u =>
        ((long).fiberLaw (principalResidueLabel period)).complexMean (fun r =>
          (allocatedLongResidueWeights B U b S period hp r hsize).complexMean
            (fun v => f p (principalAxisJoin grid u v)))) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun p => principalTupleWeights_partition_residues grid sides
        (allocatedPrincipalSides_pos B U b S) period hp hsize (f p))
    _ = (frozen).complexMean (fun u => ∫ p,
        ((long).fiberLaw (principalResidueLabel period)).complexMean (fun r =>
          (allocatedLongResidueWeights B U b S period hp r hsize).complexMean
            (fun v => f p (principalAxisJoin grid u v))) ∂μ) :=
      (frozen).integral_complexMean μ _ (fun u =>
        ((long).fiberLaw (principalResidueLabel period)).complexMean_integrable μ _ (hi u))
    _ = _ := congrArg (frozen).complexMean (funext (fun u =>
      ((long).fiberLaw (principalResidueLabel period)).integral_complexMean μ _ (hi u)))

theorem allocatedTuple_integral_comparison
    (target : PrincipalAxisTuples (α := α) grid sides →
      (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option α → ZMod period) → ℂ)
    {ε : ℝ}
    (he : ∀ u r, ‖(∫ p, (allocatedLongResidueWeights B U b S period hp r hsize).complexMean
      (fun v => f p (principalAxisJoin grid u v)) ∂μ) - target u r‖ ≤ ε) :
    ‖(∫ p, (whole).complexMean (f p) ∂μ) -
      (frozen).complexMean (fun u => ((long).fiberLaw (principalResidueLabel period)).complexMean
        (target u))‖ ≤ ε := by
  rw [allocatedTuple_integral_residues B U b S period hp hsize μ f hf]
  apply ((frozen).norm_complexMean_sub_le _ _ (fun _ => ε) ?_).trans_eq ((frozen).mean_const ε)
  intro u _
  exact (((long).fiberLaw (principalResidueLabel period)).norm_complexMean_sub_le _ _
    (fun _ => ε) (fun r _ => he u r)).trans_eq
      (((long).fiberLaw (principalResidueLabel period)).mean_const ε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_div_const {A : Type*} [Fintype A]
    (p : FiniteProbabilityWeights A) (f : A → ℂ) (Z : ℂ) :
    p.complexMean (fun a => f a / Z) = p.complexMean f / Z := by
  simp only [complexMean, mul_div_assoc, Finset.sum_div]

end Erdos3.FiniteProbabilityWeights

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "whole" => principalTupleWeights B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := α) B U b S
local notation "long" => allocatedLongTupleWeights (α := α) B U b S

variable (period : ℕ) [NeZero period] (hp : 0 < period)
variable (hsize : ∀ t, (Fintype.card α + 1) * period ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)

theorem allocatedTuple_mean_residue_comparison
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides → ℂ)
    (target : PrincipalAxisTuples (α := α) grid sides →
      (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option α → ZMod period) → ℂ)
    (error : PrincipalAxisTuples (α := α) grid sides →
      (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option α → ZMod period) → ℝ)
    (he : ∀ u r, ‖(allocatedLongResidueWeights B U b S period hp r hsize).complexMean
      (fun v => f (principalAxisJoin grid u v)) - target u r‖ ≤ error u r) :
    ‖(whole).complexMean f - (frozen).complexMean
      (fun u => ((long).fiberLaw (principalResidueLabel period)).complexMean (target u))‖ ≤
      (frozen).mean (fun u => ((long).fiberLaw (principalResidueLabel period)).mean (error u)) := by
  rw [principalTupleWeights_partition_residues grid sides (allocatedPrincipalSides_pos B U b S)
    period hp hsize f]
  apply (frozen).norm_complexMean_sub_le
  intro u _
  exact ((long).fiberLaw (principalResidueLabel period)).norm_complexMean_sub_le _ _ (error u)
    (fun r _ => he u r)

theorem allocatedTuple_normalized_residue_comparison
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides → ℂ)
    (target : PrincipalAxisTuples (α := α) grid sides →
      (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option α → ZMod period) → ℂ)
    (error : PrincipalAxisTuples (α := α) grid sides →
      (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option α → ZMod period) → ℝ)
    (Z : ℂ)
    (he : ∀ u r, ‖(allocatedLongResidueWeights B U b S period hp r hsize).complexMean
      (fun v => f (principalAxisJoin grid u v)) / Z - target u r / Z‖ ≤ error u r) :
    ‖(whole).complexMean f / Z - ((frozen).complexMean
      (fun u => ((long).fiberLaw (principalResidueLabel period)).complexMean (target u))) / Z‖ ≤
      (frozen).mean (fun u => ((long).fiberLaw (principalResidueLabel period)).mean (error u)) := by
  have h := allocatedTuple_mean_residue_comparison B U b S period hp hsize
    (fun y => f y / Z) (fun u r => target u r / Z) error
    (by simpa only [FiniteProbabilityWeights.complexMean_div_const] using he)
  simpa only [FiniteProbabilityWeights.complexMean_div_const] using h

variable {D N : Type*} [Fintype D] [Fintype N]
variable (x : G → IntegerScalarCubeBox α S.value) (spatialRoot : G → ℤ)
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))
variable (H : D → ℝ) (Q : D → N → ℝ) (hH : ∀ t, 0 < H t) (hQ : ∀ t j, 0 < Q t j)

noncomputable def allocatedOriginalSpatialOutputLaw
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides) : PMF (D → (Unit ⊕ α) → ℤ) :=
  smoothVectorSpatialOutputLaw spatialRoot (scalarCubeDifferenceMatrix x)
    (fun t => principalSpatialColumns (c t) (index t) y) H S.value Q hH
    (Nat.cast_pos.mpr S.positive) hQ

omit [DecidableEq α] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedOriginalSpatialOutputLaw_join
    (u : PrincipalAxisTuples (α := α) grid sides)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    allocatedOriginalSpatialOutputLaw B U b S x spatialRoot c index H Q hH hQ (principalAxisJoin grid u v) =
      allocatedSpatialOutputLaw B U b S u c index x spatialRoot H Q hH hQ v := rfl

theorem allocatedOriginalTuple_spatial_density_comparison
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides → (D → (Unit ⊕ α) → ℤ) → ℝ)
    (tv : Finset (D → (Unit ⊕ α) → ℤ)) (test : (D → (Unit ⊕ α) → ℤ) → ℂ)
    (target : PrincipalAxisTuples (α := α) grid sides →
      (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option α → ZMod period) → ℂ)
    (error : PrincipalAxisTuples (α := α) grid sides →
      (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option α → ZMod period) → ℝ)
    (Z : ℂ)
    (he : ∀ u r, ‖(allocatedLongResidueWeights B U b S period hp r hsize).complexMean
      (fun w => ∑ v : tv, test v.val *
        (((allocatedSpatialOutputLaw B U b S u c index x spatialRoot H Q hH hQ w v.val).toReal : ℂ) *
          (g (principalAxisJoin grid u w) v.val : ℂ))) / Z - target u r / Z‖ ≤ error u r) :
    ‖(whole).complexMean (fun y => ∑ v : tv, test v.val *
        (((allocatedOriginalSpatialOutputLaw B U b S x spatialRoot c index H Q hH hQ y v.val).toReal : ℂ) *
          (g y v.val : ℂ))) / Z - ((frozen).complexMean
      (fun u => ((long).fiberLaw (principalResidueLabel period)).complexMean (target u))) / Z‖ ≤
      (frozen).mean (fun u => ((long).fiberLaw (principalResidueLabel period)).mean (error u)) := by
  apply allocatedTuple_normalized_residue_comparison B U b S period hp hsize _ target error Z
  simpa only [allocatedOriginalSpatialOutputLaw_join] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := α) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := α) B U b S
local notation "long" => allocatedLongTupleWeights (α := α) B U b S

theorem allocatedGoodKernel_original_refined_tuple_density {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E T η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hT : 0 ≤ T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B α O P E
      ((m+1 : ℕ)*P + Fintype.card X*T)) ≤ S.value) :
    ∃ (modulus : ℕ) (hm : 0 < modulus),
      let : NeZero modulus := ⟨hm.ne'⟩
      modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∀ (q : X → ℕ), (∀ d, 0 < q d) → (∀ d, (q d : ℝ) ≤ Real.exp T) →
      let refined := residueRefinedPeriod modulus q
      ∃ hRefined : 0 < refined,
      let : NeZero refined := ⟨hRefined.ne'⟩
      (∀ d, q d * modulus ∣ refined) ∧
      (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*P + Fintype.card X*T) ∧
      ∃ hsize : ∀ d, (Fintype.card α+1)*refined ≤ lengths d,
      ∃ (reference : PrincipalAxisTuples (α := α) grid sides →
          (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
            (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined) →
          PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
        (residue : PrincipalAxisTuples (α := α) grid sides →
          (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
            (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined) →
          ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
        (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
        (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) ∧
        ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j)
        (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
        (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Module.Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
        [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides → EuclideanJetLayers U O → ℝ)
        (_hg : ∀ w, Continuous (g w)) (_hg0 : ∀ w z, 0 ≤ g w z)
        (_hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
          (euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w)
            (allocatedPhysicalCubeDirections B U b S x w) rows) =
          realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))
        (N : X → ℕ) (hN : ∀ t, 0 < N t)
    {W τ C₀ ρ ξ δ mesh : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (_hρ : 0 < ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
    (hξ : 0 < ξ) (_hξ1 : ξ ≤ 1)
    (_hphysicalSize : ∀ t, 8*(1+W)*(q t : ℝ)*ρ ≤ (ξ*τ)*(N t : ℝ))
    (_hmeshSize : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (_hρ8 : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hδ : 0 ≤ δ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ*ρ)
    (_hmesh : 0 < mesh) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (point : (X → (Unit ⊕ α) → ℤ) → EuclideanJetLayers U O)
    (test : (X → (Unit ⊕ α) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1)
    {Cg Z : ℝ} (_hCg : 0 ≤ Cg) (_hZ : 0 < Z)
    (_hcap : ∀ y v, g y (point v) ≤ Cg),
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
    let ψ := fun u r (v : X → (Unit ⊕ α) → ℤ) => ∏ t,
      spatialSiteApprox (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix
            (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u (reference u r))) modulus)))
        modulus f (H t) 4 mesh (v t)
    let A := ∏ t, ∏ i, physicalSpatialOutputScale α (H t) (T t) S.value i
    let E₀ := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M (1/(M : ℝ)) C₀ ρ ξ
    let Γ := (modulus : ℝ)^Fintype.card (Unit ⊕ α)
    let E₁ := E₀ + Γ*(anisotropicSpatialDensityLip selection (1/(M : ℝ))*(1+W))*δ
    let Esite := Fintype.card X*(E₁ + 4*Γ*(anisotropicSpatialDensityLip selection (1/(M : ℝ))*(1+W))*mesh)*
      (1 + Γ*anisotropicSpatialDensityCap selection (1/(M : ℝ)) + E₁)^Fintype.card X
    let window := spatialWindow H 4
    let F := fun u r (a : cells) => physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r))) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r))) base
      (boundedColumnResidueRepresentative q a.val) q
    let spatialBudget := fun u r (w : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) =>
      Cg*(24*(probabilityProfileLipschitz : ℝ)*Fintype.card (Option (LayerSamplerVariables G I n B) × X)/ρ)/Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a *
          ((Esite/A) * ∑ v ∈ window, ‖test (F u r a v)‖ *
            g (principalAxisJoin grid u w) (point (F u r a v)))) / Z
    let factor := fun u r (t : cells × window) =>
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ u r t.2.val / (A : ℂ)) * test (F u r t.1 t.2.val)
    let proxy := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r) (fun a => coefficientJetAxisEquiv O I n z.1 a.val) / coefficientScale))
    let error := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 * (η/coefficientScale))
    let source := fun y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides =>
      ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (g y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
    let target := fun u r => ∑ t : cells × window,
      factor u r t * (proxy u r (point (F u r t.1 t.2.val)) : ℂ)
    let budget := fun u r =>
      (allocatedLongResidueWeights B U b S refined hRefined r hsize).mean (spatialBudget u r) +
        (∑ t : cells × window, ‖factor u r t‖ * error u r (point (F u r t.1 t.2.val))) / Z
    ‖(whole).complexMean source / (Z : ℂ) -
      ((frozen).complexMean (fun u => ((long).fiberLaw (principalResidueLabel refined)).complexMean (target u))) /
        (Z : ℂ)‖ ≤
      (frozen).mean (fun u => ((long).fiberLaw (principalResidueLabel refined)).mean (budget u)) := by
  classical
  obtain ⟨modulus, hm, hdata⟩ := allocatedGoodKernel_prescribed_refined_density B U b hR hσ S x rows X
    hM selection hx hq hinj hrows hσ1 hP hE hT hη hη1 hMP hRP hRi hσi hcount hηE hlarge
  let : NeZero modulus := ⟨hm.ne'⟩
  rcases hdata with ⟨hmod, hspatial, hperiod, s, hA, hi, hstrideData⟩
  refine ⟨modulus, hm, hmod, hspatial, hperiod, s, hA, hi, ?_⟩
  intro q hqpos hqbound
  obtain ⟨hRefined, hstride, hbound, hsize, hcompare⟩ := hstrideData q hqpos hqbound
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  choose reference residue href hr hcomparison using hcompare
  refine ⟨hRefined, hstride, hbound, hsize, reference, residue, href, hr, ?_⟩
  intro _ _ _ _ hb o C hC hchart hsmall Kcov _ bW d _ μ _ _ ν _ _ g hg hg0 hlaw
    N hN W τ C₀ ρ ξ δ mesh hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hphysicalSize hmeshSize hρ8 hδ hρshift hρmove hmesh base cells hmass point test htest Cg Z hCg hZ hcap
    coefficientScale chart region H T V hV hp f ψ A E₀ Γ E₁ Esite window F spatialBudget factor proxy error source target budget
  apply allocatedTuple_normalized_residue_comparison B U b S (residueRefinedPeriod modulus q)
    hRefined hsize source target budget (Z : ℂ)
  intro u r
  exact hcomparison u r hb o C hC hchart hsmall bW d μ ν
    (fun w => g (principalAxisJoin grid u w)) (fun w => hg (principalAxisJoin grid u w))
    (fun w => hg0 (principalAxisJoin grid u w)) (fun w => hlaw (principalAxisJoin grid u w))
    N hN hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hphysicalSize hmeshSize hρ8 hδ hρshift hρmove hmesh base cells hmass point test htest hCg hZ
    (fun w _ v => hcap (principalAxisJoin grid u w) v)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal

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

def allocatedRefinedTupleMassEstimate : Prop :=
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
    let error := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 * (η/coefficientScale))
    let source := fun y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides =>
      ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (g y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
    let target := fun u r => ∑ t : cells × window,
      factor u r t * (proxy u r (point (F u r t.1 t.2.val)) : ℂ)
    let budget := fun u r =>
      Cg*(24*(probabilityProfileLipschitz : ℝ)*Fintype.card (Option (LayerSamplerVariables G I n B) × X)/ρ)/Z +
        Esite * coarseReferenceMassConstant dim X W S.value / Z +
        (∑ t : cells × window, ‖factor u r t‖ * error u r (point (F u r t.1 t.2.val))) / Z
    ‖(whole).complexMean source / (Z : ℂ) -
      ((frozen).complexMean (fun u => ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).complexMean (target u))) /
        (Z : ℂ)‖ ≤
      (frozen).mean (fun u => ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).mean (budget u))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal

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

def allocatedMassTupleStatement {M : ℕ} (_hM : 0 < M)
    (selection : (Fin dim) ↪ G) (_hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hq : Fintype.card (Fin dim) ≤ m+1) (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j o, (rows j o).card ≤ j.val+1) (_hσ1 : ∀ j, σ j ≤ 1)
    {P E T η : ℝ} (_hP : 0 ≤ P) (_hE : 0 ≤ E) (_hT : 0 ≤ T) (_hη : 0 < η) (_hη1 : η ≤ 1)
    (_hMP : (M : ℝ) ≤ Real.exp P) (_hRP : ∀ j, R j ≤ Real.exp P)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (_hηE : η⁻¹ ≤ Real.exp E)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O P E
      ((m+1 : ℕ)*P + Fintype.card X*T)) ≤ S.value) : Prop :=
    ∃ (modulus : ℕ) (hm : 0 < modulus),
      let : NeZero modulus := ⟨hm.ne'⟩
      modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ (Fin dim)) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∀ (q : X → ℕ), (∀ d, 0 < q d) → (∀ d, (q d : ℝ) ≤ Real.exp T) →
      let refined := residueRefinedPeriod modulus q
      ∃ hRefined : 0 < refined,
      let : NeZero refined := ⟨hRefined.ne'⟩
      (∀ d, q d * modulus ∣ refined) ∧
      (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*P + Fintype.card X*T) ∧
      ∃ hsize : ∀ d, (Fintype.card (Fin dim)+1)*refined ≤ lengths d,
      ∃ (reference : PrincipalAxisTuples (α := Fin dim) grid sides →
          (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
            (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
          PrincipalAxisTuples (α := Fin dim) (fun a => ¬grid a) sides)
        (residue : PrincipalAxisTuples (α := Fin dim) grid sides →
          (PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
            (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
          ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
        (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
        (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) ∧
        ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j)
        (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
        (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) C 1 j)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Module.Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
        [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides → EuclideanJetLayers U O → ℝ)
        (_hg : ∀ w, Continuous (g w)) (_hg0 : ∀ w z, 0 ≤ g w z)
        (_hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
          (euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w)
            (allocatedPhysicalCubeDirections B U b S x w) rows) =
          realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))
        (N : X → ℕ) (hN : ∀ t, 0 < N t)
    {W τ C₀ ρ ξ δ mesh : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (_hρ : 0 < ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
    (hξ : 0 < ξ) (_hξ1 : ξ ≤ 1)
    (_hphysicalSize : ∀ t, 8*(1+W)*(q t : ℝ)*ρ ≤ (ξ*τ)*(N t : ℝ))
    (_hmeshSize : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (_hρ8 : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hδ : 0 ≤ δ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ*ρ)
    (_hmesh : 0 < mesh) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (point : (X → (Unit ⊕ (Fin dim)) → ℤ) → EuclideanJetLayers U O)
    (test : (X → (Unit ⊕ (Fin dim)) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1)
    {Cg Z : ℝ} (_hCg : 0 ≤ Cg) (_hZ : 0 < Z)
    (_hcap : ∀ y v, g y (point v) ≤ Cg)
    (_hreferenceMass : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g y (point (physicalResidueReconstruction
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
          (allocatedPhysicalCubeDirections B U b S x y₀) base
          (boundedColumnResidueRepresentative q a) q v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t)),
    allocatedRefinedTupleMassEstimate B U b hR hσ S x rows X _hM selection _hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass point test Cg Z η

theorem allocatedGoodKernel_original_mass_tuple_density {M : ℕ} (hM : 0 < M)
    (selection : (Fin dim) ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card (Fin dim) ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E T η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hT : 0 ≤ T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O P E
      ((m+1 : ℕ)*P + Fintype.card X*T)) ≤ S.value) :
    allocatedMassTupleStatement B U b hR hσ S x rows X hM selection hx hq hinj hrows hσ1
      hP hE hT hη hη1 hMP hRP hRi hσi hcount hηE hlarge := by
  unfold allocatedMassTupleStatement
  classical
  obtain ⟨modulus, hm, hdata⟩ := allocatedGoodKernel_original_refined_tuple_density B U b hR hσ S x rows X
    hM selection hx hq hinj hrows hσ1 hP hE hT hη hη1 hMP hRP hRi hσi hcount hηE hlarge
  let : NeZero modulus := ⟨hm.ne'⟩
  rcases hdata with ⟨hmod, hspatial, hperiod, s, hA, hi, hstrideData⟩
  refine ⟨modulus, hm, hmod, hspatial, hperiod, s, hA, hi, ?_⟩
  intro q hqpos hqbound
  obtain ⟨hRefined, hstride, hbound, hsize, reference, residue, href, hr, hcompare⟩ :=
    hstrideData q hqpos hqbound
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hstride, hbound, hsize, reference, residue, href, hr, ?_⟩
  intro _ _ _ _ hb o C hC hchart hsmall Kcov _ bW d _ μ _ _ ν _ _ g hg hg0 hlaw
    N hN W τ C₀ ρ ξ δ mesh hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hphysicalSize hmeshSize hρ8 hδ hρshift hρmove hmesh base cells hmass point test htest Cg Z hCg hZ
    hcap hreferenceMass
  unfold allocatedRefinedTupleMassEstimate
  intro coefficientScale chart region H T V hV hp f ψ A E₀ Γ E₁ Esite
    window F factor proxy error source target budget
  have hcomparison := hcompare hb o C hC hchart hsmall bW d μ ν g hg hg0 hlaw
    N hN hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hphysicalSize hmeshSize hρ8 hδ
    hρshift hρmove hmesh base cells hmass point test htest hCg hZ hcap
  have hκ : 0 ≤ 1 / (M : ℝ) := (one_div_pos.mpr (Nat.cast_pos.mpr hM)).le
  have hE₀ : 0 ≤ E₀ := anisotropicSpatialError_nonneg selection _ M hκ
    (zero_le_one.trans hC₀) hρ.le hξ.le
  have hcap₀ := anisotropicSpatialDensityCap_nonneg selection hκ
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ
  have hEsite : 0 ≤ Esite := by dsimp only [Esite, E₁, Γ]; positivity
  have hApos : 0 < A := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hscale := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hqpos t)
    exact physicalSpatialOutputScale_pos (Fin dim) hscale.1 hscale.2 (Nat.cast_pos.mpr S.positive) i
  apply hcomparison.trans
  apply (frozen).mean_mono
  intro u
  apply ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).mean_mono
  intro r
  have h := coarse_reference_mean_spatial_budget
    (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hsize)
    q cells V hV hmass
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r)))
    (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r)))
    base H T (Nat.cast_ne_zero.mpr S.positive.ne') (fun t => trimmedSpatial_scale_ratio hW N q t)
    hApos point (fun w => g (principalAxisJoin grid u w))
    (fun w => hg0 (principalAxisJoin grid u w)) test htest
    (offset := Cg*(24*(probabilityProfileLipschitz : ℝ)*Fintype.card (Option (LayerSamplerVariables G I n B) × X)/ρ)/Z)
    hEsite hZ (fun w _ a => hreferenceMass (principalAxisJoin grid u w)
      (principalAxisJoin grid u (reference u r)) a.val)
  exact add_le_add h le_rfl

end Erdos3.VectorPolynomial

end

end OAI
