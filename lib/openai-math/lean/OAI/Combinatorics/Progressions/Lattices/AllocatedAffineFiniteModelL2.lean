import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineWholeProfileComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))

theorem allocatedRowSlicedIdeal_measurable (hR : ∀ j, 0 < R j)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (center width : input → ℝ) :
    Measurable (allocatedRowSlicedIdeal B U b S rowSets ρ center width) := by
  apply diagonalImageDensity_measurable (fun q : output => R q.1.val.1)
    (fun q : output => (hR q.1.val.1).ne')
  exact (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => (Subtype.val : jets a.val.1 → Finset α))
    ρ hρ center width).2.1.continuous.measurable

theorem allocatedRowSlicedIdeal_coordinate_support (hR : ∀ j, 0 < R j)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : input → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    (v : output → ℝ) (hv : allocatedRowSlicedIdeal B U b S rowSets ρ center width v ≠ 0)
    (a : {a // ¬grid a}) (t : jets a.val.1) :
    |v ⟨a, t⟩| ≤ (partitionedIdealRadius α m + 1) * R a.val.1 := by
  have hn : ‖fun q : output => v q / R q.1.val.1‖ ≤ partitionedIdealRadius α m + 1 := by
    by_contra hh
    apply hv
    unfold allocatedRowSlicedIdeal diagonalImageDensity
    rw [activeAveragedSlicedProfileIdeal_zero_outside (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a => (Subtype.val : jets a.val.1 → Finset α))
      (fun a => Nat.succ_le_of_lt a.1.isLt) ρ hρ hρ1 center width hw _ (lt_of_not_ge hh), mul_zero]
  have hc := (norm_le_pi_norm (fun q : output => v q / R q.1.val.1) ⟨a, t⟩).trans hn
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hR a.val.1)] at hc
  exact (div_le_iff₀ (hR a.val.1)).mp hc

theorem allocatedRowSlicedIdeal_normalized_cap (hR : ∀ j, 0 < R j)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (center width : input → ℝ)
    (z : AllocatedLongJetRows B U b S jets) :
    ‖((∏ q : output, R q.1.val.1 : ℝ) : ℂ) *
      (allocatedRowSlicedIdeal B U b S rowSets ρ center width
        (allocatedLongJetRealCoordinates B U b S z) : ℂ)‖ ≤
      (ρ⁻¹ ^ Fintype.card output : ℝ≥0) := by
  rw [← Complex.ofReal_mul, allocatedRowSlicedIdealCoordinates_density B U b S rowSets hR ρ center width]
  have hb := (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => (Subtype.val : jets a.val.1 → Finset α)) ρ hρ center width).1
    (booleanSiteJets (fun a => (Subtype.val : jets a.val.1 → Finset α))
      (fun s a => allocatedRowIdealCoordinates B U b S rowSets z s a.val))
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
variable (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
variable (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hT hsource hradius hC hchart hbudget in

theorem allocatedAffineRowIdeal_cutoff_fixes
    (hσ1 : ∀ j, σ j ≤ 1) (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
      (α := α) (fun a => ¬grid a) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (x : G → IntegerScalarCubeBox α S.value)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (y : EuclideanJetLayers U rowTypes) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y *
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y : ℂ) =
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y : ℂ) := by
  apply allocatedProductSiteCutoff_fixes_source B U b S rowSets o hb bW d r hr hR hσ T hT hsource hradius C hC hchart hbudget hσ1 x y₀ q
  intro v hv a₀ t
  exact (allocatedRowSlicedIdeal_coordinate_support B U b S rowSets hR ρ hρ hρ1 center width hw v hv a₀ t).trans (mul_le_mul_of_nonneg_right (hTideal _) (hR _).le)

include hT hsource hradius hC hchart hbudget in

theorem allocatedAffineRowIdeal_cutoff_fixes_mean
    (hσ1 : ∀ j, σ j ≤ 1) (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
      (α := α) (fun a => ¬grid a) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (x : G → IntegerScalarCubeBox α S.value)
    {Ω : Type*} [Fintype Ω] (weights : FiniteProbabilityWeights Ω)
    (tuples : Ω → PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (y : EuclideanJetLayers U rowTypes) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y *
      ((weights).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (tuples u) q
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y) : ℂ) =
      ((weights).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (tuples u) q
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y) : ℂ) := by
  simp only [← weights.complexMean_ofReal]
  rw [← weights.complexMean_mul_left]
  apply congrArg weights.complexMean
  funext u
  exact allocatedAffineRowIdeal_cutoff_fixes B U b S rowSets o hb bW d r hr hR hσ T hT hsource hradius C hC hchart hbudget
    hσ1 hTideal ρ hρ hρ1 center width hw x (tuples u) q y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hperiod hM hm hR hC hchart hbudget in

theorem allocatedAffineProductPrefactor_cap
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
      (α := α) (fun a => ¬grid a) → ℝ)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y‖ ≤
      ‖inverseNormalizer‖ * (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) *
        (ρ⁻¹ ^ Fintype.card (Σ a : {a // ¬grid a}, rowTypes a.val.1) : ℝ≥0) := by
  let aa : Empty → ℂ := fun i => i.elim
  let ff : Empty → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ := fun i => i.elim
  have herr (v : AllocatedLongJetRows B U b S rowTypes) :
      ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
          (allocatedRowSlicedIdeal B U b S rowSets ρ center width
            (allocatedLongJetRealCoordinates B U b S v) : ℂ) -
        ∑ k, aa k * ∏ s, ff k s (allocatedRowIdealCoordinates B U b S rowSets v s)‖ ≤
      (ρ⁻¹ ^ Fintype.card (Σ a : {a // ¬grid a}, rowTypes a.val.1) : ℝ≥0) := by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact allocatedRowSlicedIdeal_normalized_cap B U b S rowSets hR ρ hρ center width _
  have he := allocatedProductChartDensityApproximation_error B U b S rowSets x y₀ q d period r hr hb o bW
    hperiod hM hm hR C hC hchart hbudget aa ff
    (allocatedRowSlicedIdeal B U b S rowSets ρ center width)
    (NNReal.coe_nonneg _) herr y
  simpa only [allocatedProductChartIdealApproximation, Finset.univ_eq_empty, Finset.sum_empty,
    Finset.sum_const_zero, sub_zero] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, ↥(rowSets j) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowSets j → Finset α)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := ↥(rowSets j))
  S.positive x (j.val + 1) (Subtype.val : rowSets j → Finset α) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : EuclideanJetLayers U (fun j => ↥(rowSets j)) → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d (fun p => F (Prod.snd p))
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ j, Nonempty (rowSets j)] in
theorem allocatedAffineFiniteModel_comparison
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let _outputResidue := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    ∀ (period : ℕ) [NeZero period] (r : ℝ≥0) (hr : 0 < r)
      (u₀ : GridTuples) {Kmodel : Type*} [Fintype Kmodel]
      (am : Kmodel → ℂ) (fm : Kmodel → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
      {Lm : ℝ≥0} (_hLm : ∀ k t, LipschitzWith Lm (fm k t)) (_hfm : ∀ k t z, ‖fm k t z‖ ≤ 1)
      (eg : {a // grid a} → ScalarSiteExpansion (Finset α))
      {Nt V Cc Hs : {a // grid a} → ℝ} {Lg : ℝ≥0}
      (_heg : ∀ a, (eg a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)) {εmodel : ℝ},
      (∀ y : EuclideanJetLayers U selectedRows,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
          hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ) -
          (allocatedProductChartIdealApproximation B U basis S rowSets x (principalAxisJoin grid u₀ v₀)
            modulus d period r hr hb o bW am fm y *
            allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y)‖ ≤ εmodel) →
      ‖actual - ∫ y, (allocatedProductChartIdealApproximation B U basis S rowSets x
        (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW am fm y *
        allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α selectedRows P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α selectedRows P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α selectedRows (ρ grid) P η (fun _ => modulus) H ε mesh Cmask + εmodel
 := by
  intro center width ideal outputResidue period hperiodNZ r hr u₀ Kmodel hKmodel am fm Lm hLm hfm eg Nt V Cc Hs Lg heg εmodel happrox
  have hc := allocatedAffineWholeProfile_comparison B U basis hR hσ S rows x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d F H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ν
    ρ t htone hs hρ hρ1 hσsmall hstep hH hδ hdense hm hsize hsmall hε hmesh
    selection hgood hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask
    T hT hsource C hC hchart hbudget hF hFbound
  have hs' := allocatedWholeMaskedCoveredProfile_mean_measurable B U basis hR hσ S x rows hb o bW d
    gridLaw (fun u => principalAxisJoin grid u v₀) modulus ideal
    (allocatedRowSlicedIdeal_measurable B U basis S rowSets hR (ρ grid) hρ center width)
  have ht := allocatedFiniteSourceModel_test_error B U basis S rowSets x (principalAxisJoin grid u₀ v₀)
    modulus d period r hr hb o bW (Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j)))
    am fm hLm hfm eg heg _ hs' happrox F hF hFbound
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hc ht.2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, ↥(rowSets j) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowSets j → Finset α)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := ↥(rowSets j))
  S.positive x (j.val + 1) (Subtype.val : rowSets j → Finset α) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ j, Nonempty (rowSets j)] in
theorem allocatedAffineFiniteModel_l1
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) ξ)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure ξ (g y))
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let _outputResidue := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    ∀ (period : ℕ) [NeZero period] (r : ℝ≥0) (hr : 0 < r)
      (u₀ : GridTuples) {Kmodel : Type*} [Fintype Kmodel]
      (am : Kmodel → ℂ) (fm : Kmodel → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
      {Lm : ℝ≥0} (_hLm : ∀ k t, LipschitzWith Lm (fm k t)) (_hfm : ∀ k t z, ‖fm k t z‖ ≤ 1)
      (eg : {a // grid a} → ScalarSiteExpansion (Finset α))
      {Nt V Cc Hs : {a // grid a} → ℝ} {Lg : ℝ≥0}
      (_heg : ∀ a, (eg a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)) {εmodel : ℝ},
      (∀ y : EuclideanJetLayers U selectedRows,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
          hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ) -
          (allocatedProductChartIdealApproximation B U basis S rowSets x (principalAxisJoin grid u₀ v₀)
            modulus d period r hr hb o bW am fm y *
            allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y)‖ ≤ εmodel) →
      (∫ y, ‖((wholeLaw).mean (fun v => g v y) : ℂ) -
        (allocatedProductChartIdealApproximation B U basis S rowSets x
          (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW am fm y *
          allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y)‖ ∂ξ) ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α selectedRows P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α selectedRows P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α selectedRows (ρ grid) P η (fun _ => modulus) H ε mesh Cmask + εmodel
 := by
  intro center width ideal outputResidue period hperiodNZ r hr u₀ Kmodel hKmodel am fm Lm hLm hfm eg Nt V Cc Hs Lg heg εmodel happrox
  let model := fun y => allocatedProductChartIdealApproximation B U basis S rowSets x
    (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW am fm y *
      allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y
  have hmodelm : Measurable model :=
    (allocatedProductChartIdealApproximation_measurable B U basis S rowSets x
      (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW am fm hLm hfm).mul
      (allocatedFullGridChartModel_measurable B U basis S rowSets d hb o bW eg)
  have hmodeli : Integrable model ξ := allocatedFiniteSourceModel_integrable B U basis S rowSets x
    (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW ξ am fm hLm hfm eg heg
  have hmeanm : Measurable (fun y => ((wholeLaw).mean (fun v => g v y) : ℂ)) :=
    (Finset.measurable_sum Finset.univ (fun v _ => (hgm v).const_mul _)).complex_ofReal
  have hmeani : Integrable (fun y => ((wholeLaw).mean (fun v => g v y) : ℂ)) ξ :=
    (integrable_finsetSum Finset.univ (fun v _ => (hgi v).const_mul _)).ofReal
  apply complex_model_l1_le_of_bounded_tests ξ _ model hmeanm hmodelm hmeani hmodeli
  intro F hF hFbound
  have hc := allocatedAffineFiniteModel_comparison B U basis hR hσ S rowSets x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d F H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ν
    ρ t htone hs hρ hρ1 hσsmall hstep hH hδ hdense hm hsize hsmall hε hmesh
    selection hgood hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask
    T hT hsource C hC hchart hbudget hF hFbound
    period r hr u₀ am fm hLm hfm eg heg happrox
  have hsmallDensity (j) : C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4 := by
    have hT1 : 1 ≤ T j := (le_add_of_nonneg_left (partitionedIdealRadius_nonneg α m)).trans (hT j)
    have hRle : R j ≤ T j * R j := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hT1 (hR j).le
    calc
      _ = C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := mul_assoc _ _ _
      _ ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRle
          (add_nonneg (Nat.cast_nonneg _) zero_le_one)) (hC j)
      _ ≤ _ := hbudget j
  have hdeck := allocatedCoefficientDeckSample_density_law B U basis hR hσ S Q hb o bW d μ ν
    (fun j => (hσsmall j).trans htone) C hC hchart hsmallDensity
  have hid := allocatedProgressionCoveredExpectation_density B U basis hR hσ S rows x Q hb o bW d
    H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell μ ν hdeck g hgm hg0 hgi hglaw F hF hFbound
  rw [hid] at hc
  exact hc

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, ↥(rowSets j) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowSets j → Finset α)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := ↥(rowSets j))
  S.positive x (j.val + 1) (Subtype.val : rowSets j → Finset α) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ j, Nonempty (rowSets j)] in
theorem allocatedAffineFiniteModel_l2
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) ξ)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure ξ (g y))
    (densityCap : ℝ≥0) (hgcap : ∀ y z, |g y z| ≤ densityCap)
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let _outputResidue := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    ∀ (period : ℕ) [NeZero period] (r : ℝ≥0) (hr : 0 < r)
      (u₀ : GridTuples) {Kmodel : Type*} [Fintype Kmodel]
      (am : Kmodel → ℂ) (fm : Kmodel → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
      {Lm : ℝ≥0} (_hLm : ∀ k t, LipschitzWith Lm (fm k t)) (_hfm : ∀ k t z, ‖fm k t z‖ ≤ 1)
      (eg : {a // grid a} → ScalarSiteExpansion (Finset α))
      {Nt V Cc Hs : {a // grid a} → ℝ} {Lg : ℝ≥0}
      (_heg : ∀ a, (eg a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)) {εmodel : ℝ}
      (profileCap : ℝ≥0)
      (_hprofileCap : ∀ u y, |allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u v₀) modulus ideal y| ≤ profileCap),
      (∀ y : EuclideanJetLayers U selectedRows,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
          hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ) -
          (allocatedProductChartIdealApproximation B U basis S rowSets x (principalAxisJoin grid u₀ v₀)
            modulus d period r hr hb o bW am fm y *
            allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y)‖ ≤ εmodel) → εmodel ≤ 1 →
      (∫ y, ‖((wholeLaw).mean (fun v => g v y) : ℂ) -
        (allocatedProductChartIdealApproximation B U basis S rowSets x
          (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW am fm y *
          allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y)‖ ^ 2 ∂ξ) ≤
      ((densityCap + (profileCap + 1) : ℝ≥0) : ℝ) *
      ((2 * Real.exp (allocatedJetSupportLog (G := G) B α selectedRows P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α selectedRows P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α selectedRows (ρ grid) P η (fun _ => modulus) H ε mesh Cmask + εmodel)
 := by
  intro center width ideal outputResidue period hperiodNZ r hr u₀ Kmodel hKmodel am fm Lm hLm hfm eg Nt V Cc Hs Lg heg εmodel profileCap hprofileCap happrox hεmodel
  let model := fun y => allocatedProductChartIdealApproximation B U basis S rowSets x
    (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW am fm y *
      allocatedFullGridChartModel B U basis S rowSets d hb o bW eg y
  have hmodelm : Measurable model :=
    (allocatedProductChartIdealApproximation_measurable B U basis S rowSets x
      (principalAxisJoin grid u₀ v₀) modulus d period r hr hb o bW am fm hLm hfm).mul
      (allocatedFullGridChartModel_measurable B U basis S rowSets d hb o bW eg)
  have hmeanm : Measurable (fun y => ((wholeLaw).mean (fun v => g v y) : ℂ)) :=
    (Finset.measurable_sum Finset.univ (fun v _ => (hgm v).const_mul _)).complex_ofReal
  have hmeanb (y) : ‖((wholeLaw).mean (fun v => g v y) : ℂ)‖ ≤ densityCap := by
    rw [← FiniteProbabilityWeights.complexMean_ofReal]
    have hb (v) : ‖(g v y : ℂ)‖ ≤ densityCap := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hgcap v y
    exact ((wholeLaw).norm_complexMean_le_mean_norm _).trans
      (((wholeLaw).mean_mono hb).trans_eq ((wholeLaw).mean_const _))
  have hmodelb (y) : ‖model y‖ ≤ (profileCap + 1 : ℝ≥0) := by
    simpa only [NNReal.coe_add, NNReal.coe_one] using
      finiteMeanModel_norm_le_of_uniform_approximation (gridLaw)
        (fun u y => allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
          hb o bW d (principalAxisJoin grid u v₀) modulus ideal y)
        model hprofileCap happrox hεmodel y
  have hL1 := allocatedAffineFiniteModel_l1 B U basis hR hσ S rowSets x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ν μ
    g hgm hg0 hgi hglaw ρ t htone hs hρ hρ1 hσsmall hstep hH hδ hdense hm hsize hsmall hε hmesh
    selection hgood hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask
    T hT hsource C hC hchart hbudget period r hr u₀ am fm hLm hfm eg heg happrox
  exact complex_model_l2_le_of_l1 ξ _ model hmeanm hmodelm densityCap (profileCap + 1)
    hmeanb hmodelb hL1

end Erdos3.VectorPolynomial

end

end OAI
