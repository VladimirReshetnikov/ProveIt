import OAI.Combinatorics.Progressions.Estimates.AllocatedEarlyWindowVolume
import OAI.Combinatorics.Progressions.Lattices.AllocatedGridlessMeasurableResidue

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" z => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z
local notation "dirs" z => allocatedPhysicalCubeDirections B U b S x z

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (M : ℕ)

local notation "split" => coefficientJetAxisSplit O I n grid
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "residue" => fun j => integerResidueMatrix
  (allocatedNonkernelJetMatrix B U b S x (principalAxisRestrict grid y) rows j
    (principalAxisRestrict (fun a => ¬grid a) y)) M

theorem allocatedWholeMaskedGridlessProfile_window_mass
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (χ : EuclideanJetLayers U O → ℝ)
    (hχ : ∀ z ∈ region, χ (chart z) = allocatedGridWindowWeight B U b S O selected W p ((split z.1).1))
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
    (hf : Measurable f) {T C Cf : ℝ}
    (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hfb : ∀ v, |f v| ≤ Cf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j M ((residue) j) z ∧
      allocatedIntegerKernelMask B U b S x rows j M ((residue) j) z ≤ C) :
    Integrable (fun z => χ z * allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d M f z) haar ∧
      (∫ z, |χ z * allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d M f z| ∂haar) ≤
        (∏ a, if selected a then ((W a).card : ℝ) else 1) *
          ((C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
            (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) := by
  have hw := allocatedGridWindowWeight_mass_data B U b S O selected W p
  have hwm := allocatedGridWindowWeight_measurable B U b S O selected W p
  have hl := allocatedLongProfileDensity_integrable B U b S x rows M (residue) f hf hT hs hC hCf hfb hm
  have hlm := allocatedLongProfileDensity_measurable B U b S x rows M (residue) f hf
  have hbnd := allocatedLongProfileDensity_integral_abs_bound B U b S x rows M (residue) f hf hT hs hC hCf hfb hm
  have he := allocatedGridlessCoveredProfile_weighted_mass B U b S x
    (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y)
    rows hb o bW d ν (allocatedGridWindowWeight B U b S O selected W p)
    (allocatedLongProfileDensity B U b S x rows M (residue) f) χ hχ hwm hlm hw.1 hl
  refine ⟨he.1, ?_⟩
  have hbound := he.2
  rw [hw.2] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left hbnd (Finset.prod_nonneg (fun _ _ => by
    split_ifs <;> positivity)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

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

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "tuples" => principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

noncomputable def allocatedWholeMaskedCoveredProfile
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  allocatedCoveredProfileDensity B U b hR hσ S x (principalAxisRestrict grid y)
    (principalAxisRestrict (fun a => ¬grid a) y) rows hb o bW d quarter
    (allocatedLongProfileDensity B U b S x rows q
      (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
        (principalAxisRestrict grid y) rows j (principalAxisRestrict (fun a => ¬grid a) y)) q) f)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] in
theorem allocatedWholeMaskedCoveredProfile_grid_multiplier
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f =
      fun z => allocatedChartGridMultiplier B U b S O hb o bW d
        (allocatedGridJetDensity B U b hR hσ S x (principalAxisRestrict grid y)
          (principalAxisRestrict (fun a => ¬grid a) y) rows) z *
            allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d q f z :=
  allocatedCoveredProfileDensity_grid_multiplier B U b S O hb o bW d hR hσ x
    (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y) rows _

variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

theorem allocatedWholeMaskedCoveredProfile_conditional_mean
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
    (z : EuclideanJetLayers U O) :
    (FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) =
      allocatedChartGridMultiplier B U b S O hb o bW d
        (allocatedSupportedGridJetDensity B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell) z *
          allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f z := by
  simp_rw [allocatedWholeMaskedCoveredProfile_grid_multiplier]
  have hsame : (FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean (fun y =>
      allocatedChartGridMultiplier B U b S O hb o bW d
        (allocatedGridJetDensity B U b hR hσ S x (principalAxisRestrict grid y)
          (principalAxisRestrict (fun a => ¬grid a) y) rows) z *
            allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d q f z) =
      (FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean (fun y =>
        allocatedChartGridMultiplier B U b S O hb o bW d
          (allocatedGridJetDensity B U b hR hσ S x (principalAxisRestrict grid y)
            (principalAxisRestrict (fun a => ¬grid a) y) rows) z *
              allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f z) := by
    apply (FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean_congr_on_support
    intro y hy
    have hlabel := (Finset.mem_filter.mp (condition_weight_support (tuples) _ hcell y hy).1).2
    rw [allocatedWholeMaskedGridlessProfile_eq B U b S x y y₀ rows hb o bW d q hperiod hlabel]
  rw [hsame, (FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean_mul_const]
  have hmean := congrFun (allocatedChartGridMultiplier_mean B U b S O hb o bW d (FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell)
    (fun y => allocatedGridJetDensity B U b hR hσ S x (principalAxisRestrict grid y)
      (principalAxisRestrict (fun a => ¬grid a) y) rows)) z
  simp_rw [allocatedGridJetDensity_conditional_mean B U b hR hσ S x rows q
    (principalResidueLabel q y₀) hcell] at hmean
  rw [hmean]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" z => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z
local notation "dirs" z => allocatedPhysicalCubeDirections B U b S x z

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (M : ℕ)

local notation "split" => coefficientJetAxisSplit O I n grid
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "residue" => fun j => integerResidueMatrix
  (allocatedNonkernelJetMatrix B U b S x (principalAxisRestrict grid y) rows j
    (principalAxisRestrict (fun a => ¬grid a) y)) M

theorem allocatedWholeMaskedGridlessProfile_window_integral_mass
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (χ : EuclideanJetLayers U O → ℝ)
    (hχ : ∀ z ∈ region, χ (chart z) = allocatedGridWindowWeight B U b S O selected W p ((split z.1).1))
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
    (hf : Measurable f)
    (hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S f) (allocatedLongJetReference B U b S O))
    {C Mf : ℝ} (hC : 1 ≤ C)
    (hMf : (∫ z, |allocatedUnmaskedLongProfileDensity B U b S f z| ∂allocatedLongJetReference B U b S O) ≤ Mf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j M ((residue) j) z ∧
      allocatedIntegerKernelMask B U b S x rows j M ((residue) j) z ≤ C) :
    Integrable (fun z => χ z * allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d M f z) haar ∧
      (∫ z, |χ z * allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d M f z| ∂haar) ≤
        (∏ a, if selected a then ((W a).card : ℝ) else 1) *
          (C ^ Fintype.card (LayerSamplerAxis I n) * Mf) := by
  have hw := allocatedGridWindowWeight_mass_data B U b S O selected W p
  have hwm := allocatedGridWindowWeight_measurable B U b S O selected W p
  have hl := allocatedLongProfileDensity_integral_mass B U b S x rows M (residue) f hf hi hC hm
  have hlm := allocatedLongProfileDensity_measurable B U b S x rows M (residue) f hf
  have he := allocatedGridlessCoveredProfile_weighted_mass B U b S x
    (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y)
    rows hb o bW d ν (allocatedGridWindowWeight B U b S O selected W p)
    (allocatedLongProfileDensity B U b S x rows M (residue) f) χ hχ hwm hlm hw.1 hl.1
  refine ⟨he.1, ?_⟩
  have hlong := hl.2.trans (mul_le_mul_of_nonneg_left hMf (pow_nonneg (zero_le_one.trans hC) _))
  have hbound := he.2
  rw [hw.2] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left hlong (Finset.prod_nonneg (fun _ _ => by
    split_ifs <;> positivity)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

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
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop) [DecidablePred selected]
variable (W : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, Finset (CoefficientJetAxisRow O a.val))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
variable (hf : Measurable f) {T C Cf : ℝ}
variable (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
variable (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hfb : ∀ v, |f v| ≤ Cf)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "density" => allocatedSupportedGridJetDensity B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "weight" => allocatedGridWindowWeight B U b S O selected W laws
local notation "χ" => allocatedChartGridMultiplier B U b S O hb o bW d weight
local notation "profile" => allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "massBound" => (∏ a : {a // allocatedGridAxis (I := I) U b S.value a},
  ite (selected a) (Nat.cast (Finset.card (W a)) : ℝ) 1) *
  ((C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
    (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a)))
local notation "residue" => fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q

variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x rows j q (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ C)

include hf hT hs hC hCf hfb hm in
theorem allocatedConditionalWindow_mass :
    Integrable (fun z => χ z * profile z) haar ∧
      (∫ z, |χ z * profile z| ∂haar) ≤ massBound := by
  exact allocatedWholeMaskedGridlessProfile_window_mass B U b S x y₀ rows hb o bW d ν q
    selected W laws χ (allocatedChartGridMultiplier_apply B U b S O hb o bW d weight)
    f hf hT hs hC hCf hfb hm

include hf hT hs hC hCf hfb hm in
theorem allocatedConditionalProfile_haar_error
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (g : AllocatedFrozenJetRows B U b S O → ℂ) (hg : Measurable g)
    {E : ℝ} (hE : 0 ≤ E) (he : ∀ z, ‖(density z : ℂ) - g z‖ ≤ E * weight z) :
    Integrable (fun z =>
      ((FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
        allocatedComplexGridMultiplier B U b S O hb o bW d g z * (profile z : ℂ)) haar ∧
    (∫ z, ‖((FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
        allocatedComplexGridMultiplier B U b S O hb o bW d g z * (profile z : ℂ)‖ ∂haar) ≤ E * massBound := by
  simp_rw [allocatedWholeMaskedCoveredProfile_conditional_mean B U b hR hσ S x rows hb o bW d q y₀ hcell hperiod f]
  let a := allocatedChartGridMultiplier B U b S O hb o bW d density
  let c := allocatedComplexGridMultiplier B U b S O hb o bW d g
  let D : EuclideanJetLayers U O → ℂ := fun z => ((a z * profile z : ℝ) : ℂ) - c z * (profile z : ℂ)
  change Integrable D haar ∧ (∫ z, ‖D z‖ ∂haar) ≤ E * massBound
  have hdm : Measurable density := by
    change Measurable (fun z : AllocatedFrozenJetRows B U b S O => ∏ a, ((laws a) (z a)).toReal)
    exact Finset.measurable_prod _ (fun a _ =>
      (measurable_of_countable (fun z => ((laws a) z).toReal)).comp (measurable_pi_apply a))
  have ham : Measurable a := allocatedChartGridMultiplier_measurable B U b S O hb o bW d density hdm
  have hcm : Measurable c := allocatedComplexGridMultiplier_measurable B U b S O hb o bW d g hg
  have hpm : Measurable profile :=
    allocatedWholeMaskedGridlessProfile_measurable B U b S x y₀ rows hb o bW d q f hf
  have hDm : Measurable D := ((ham.mul hpm).complex_ofReal).sub (hcm.mul hpm.complex_ofReal)
  have hw := allocatedConditionalWindow_mass B U b hR hσ S x rows hb o bW d ν q y₀ hcell selected W f hf hT hs hC hCf hfb hm
  have hχ (z : EuclideanJetLayers U O) : 0 ≤ χ z :=
    allocatedChartGridMultiplier_nonneg B U b S O hb o bW d weight
      (allocatedGridWindowWeight_nonneg B U b S O selected W laws) z
  have hbnd (z : EuclideanJetLayers U O) : ‖D z‖ ≤ E * |χ z * profile z| := by
    have heq : D z = ((a z : ℂ) - c z) * (profile z : ℂ) := by
      dsimp only [D]
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ z)]
    exact (mul_le_mul_of_nonneg_right
      (allocatedGridMultiplier_error B U b S O hb o bW d density g weight E he z)
      (abs_nonneg (profile z))).trans_eq (mul_assoc E (χ z) |profile z|)
  have hmajor : Integrable (fun z => E * |χ z * profile z|) haar := by
    simpa only [Real.norm_eq_abs] using hw.1.norm.const_mul E
  have hDi : Integrable D haar := hmajor.mono' hDm.aestronglyMeasurable (ae_of_all _ hbnd)
  refine ⟨hDi, ?_⟩
  calc
    (∫ z, ‖D z‖ ∂haar) ≤ ∫ z, E * |χ z * profile z| ∂haar := integral_mono hDi.norm hmajor hbnd
    _ = E * ∫ z, |χ z * profile z| ∂haar := integral_const_mul _ _
    _ ≤ E * massBound := mul_le_mul_of_nonneg_left hw.2 hE

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

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
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop) [DecidablePred selected]
variable (W : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, Finset (CoefficientJetAxisRow O a.val))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
variable (hf : Measurable f) {T C Cf : ℝ}
variable (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
variable (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hfb : ∀ v, |f v| ≤ Cf)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "density" => allocatedSupportedGridJetDensity B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "weight" => allocatedGridWindowWeight B U b S O selected W laws
local notation "χ" => allocatedChartGridMultiplier B U b S O hb o bW d weight
local notation "profile" => allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "massBound" => (∏ a : {a // allocatedGridAxis (I := I) U b S.value a},
  ite (selected a) (Nat.cast (Finset.card (W a)) : ℝ) 1) *
  ((C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
    (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a)))
local notation "residue" => fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q

variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x rows j q (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ C)

local notation "longBound" => (C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
  (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))

include hf hT hs hC hCf hfb hm in
theorem allocatedConditionalProfile_selected_haar_error
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (g : AllocatedFrozenJetRows B U b S O → ℂ) (hg : Measurable g)
    {N ε V : ℝ} (hN : 0 < N) (hε : 0 ≤ ε)
    (hcard : (∏ a, if selected a then ((W a).card : ℝ) else 1) ≤ V * N)
    (hzero : ∀ z, (¬∀ a, selected a → z a ∈ W a) →
      allocatedSelectedGridMass B U b S O selected laws z = 0 ∧ g z = 0)
    (he : ∀ z, ‖(N : ℂ) * (allocatedSelectedGridMass B U b S O selected laws z : ℂ) - g z‖ ≤ ε) :
    Integrable (fun z =>
      ((FiniteProbabilityWeights.condition
        (principalTupleWeights (α := α) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
          (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
      allocatedComplexGridMultiplier B U b S O hb o bW d
        (allocatedPartialGridApproximation B U b S O selected laws N g) z * (profile z : ℂ)) haar ∧
    (∫ z, ‖((FiniteProbabilityWeights.condition
        (principalTupleWeights (α := α) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
          (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
      allocatedComplexGridMultiplier B U b S O hb o bW d
        (allocatedPartialGridApproximation B U b S O selected laws N g) z * (profile z : ℂ)‖ ∂haar) ≤
      (ε * V) * longBound := by
  have hmG := allocatedPartialGridApproximation_measurable B U b S O selected laws N g hg
  have herr (z : AllocatedFrozenJetRows B U b S O) :=
    allocatedPartialGridApproximation_error B U b S O selected laws W g hN hzero he z
  have h := allocatedConditionalProfile_haar_error B U b hR hσ S x rows hb o bW d ν q y₀ hcell
    selected W f hf hT hs hC hCf hfb hm hperiod
    (allocatedPartialGridApproximation B U b S O selected laws N g) hmG (div_nonneg hε hN.le) herr
  refine ⟨h.1, h.2.trans ?_⟩
  have hb : 0 ≤ longBound := by
    have hc : 0 ≤ C := zero_le_one.trans hC
    positivity
  calc
    (ε / N) * massBound ≤ (ε / N) * ((V * N) * longBound) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hb) (div_nonneg hε hN.le)
    _ = (ε * V) * longBound := by field_simp [hN.ne']

include hf hT hs hC hCf hfb hm in
theorem allocatedConditionalProfile_natural_haar_error
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (g : AllocatedFrozenJetRows B U b S O → ℂ) (hg : Measurable g)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hzero : ∀ z, (¬∀ a, selected a → z a ∈ allocatedFrozenNaturalWindow B U b S α O a) →
      allocatedSelectedGridMass B U b S O selected laws z = 0 ∧ g z = 0)
    (he : ∀ z, ‖(allocatedSelectedNaturalVolume B U b S O selected : ℂ) *
      (allocatedSelectedGridMass B U b S O selected laws z : ℂ) - g z‖ ≤ ε) :
    Integrable (fun z =>
      ((FiniteProbabilityWeights.condition
        (principalTupleWeights (α := α) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
          (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
      allocatedComplexGridMultiplier B U b S O hb o bW d
        (allocatedPartialGridApproximation B U b S O selected laws
          (allocatedSelectedNaturalVolume B U b S O selected) g) z * (profile z : ℂ)) haar ∧
    (∫ z, ‖((FiniteProbabilityWeights.condition
        (principalTupleWeights (α := α) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
          (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
      allocatedComplexGridMultiplier B U b S O hb o bW d
        (allocatedPartialGridApproximation B U b S O selected laws
          (allocatedSelectedNaturalVolume B U b S O selected) g) z * (profile z : ℂ)‖ ∂haar) ≤
      (ε * allocatedSelectedNaturalWindowVolume B U b S α O selected) * longBound := by
  exact allocatedConditionalProfile_selected_haar_error B U b hR hσ S x rows hb o bW d ν q y₀ hcell
    selected (allocatedFrozenNaturalWindow B U b S α O) f hf hT hs hC hCf hfb hm hperiod g hg
    (allocatedSelectedNaturalVolume_pos B U b S O hR selected) hε
    (allocatedFrozenNaturalWindow_selected_card_le B U b S α O hR selected) hzero he

include hf hT hs hC hCf hfb hm in
theorem allocatedConditionalProfile_budgeted_haar_error
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (g : AllocatedFrozenJetRows B U b S O → ℂ) (hg : Measurable g)
    {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ z, (¬∀ a, selected a → z a ∈ allocatedFrozenNaturalWindow B U b S α O a) →
      allocatedSelectedGridMass B U b S O selected laws z = 0 ∧ g z = 0)
    (he : ∀ z, ‖(allocatedSelectedNaturalVolume B U b S O selected : ℂ) *
      (allocatedSelectedGridMass B U b S O selected laws z : ℂ) - g z‖ ≤ δ / (allocatedGridWindowEarlyVolume (G := G) B α O + 1)) :
    Integrable (fun z =>
      ((FiniteProbabilityWeights.condition
        (principalTupleWeights (α := α) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
          (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
      allocatedComplexGridMultiplier B U b S O hb o bW d
        (allocatedPartialGridApproximation B U b S O selected laws
          (allocatedSelectedNaturalVolume B U b S O selected) g) z * (profile z : ℂ)) haar ∧
    (∫ z, ‖((FiniteProbabilityWeights.condition
        (principalTupleWeights (α := α) B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
          (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
      allocatedComplexGridMultiplier B U b S O hb o bW d
        (allocatedPartialGridApproximation B U b S O selected laws
          (allocatedSelectedNaturalVolume B U b S O selected) g) z * (profile z : ℂ)‖ ∂haar) ≤
      δ * longBound := by
  let V := allocatedGridWindowEarlyVolume (G := G) B α O
  have hV : 0 ≤ V := allocatedGridWindowEarlyVolume_nonneg (G := G) B α O
  have hVp : 0 < V + 1 := by linarith
  have hε : 0 ≤ δ / (V + 1) := div_nonneg hδ.le hVp.le
  have h := allocatedConditionalProfile_natural_haar_error B U b hR hσ S x rows hb o bW d ν q y₀ hcell
    selected f hf hT hs hC hCf hfb hm hperiod g hg hε hzero he
  refine ⟨h.1, h.2.trans ?_⟩
  have hlong : 0 ≤ longBound := by
    have hc : 0 ≤ C := zero_le_one.trans hC
    positivity
  have heV : δ / (V + 1) * V ≤ δ := by
    calc
      _ ≤ δ / (V + 1) * (V + 1) := mul_le_mul_of_nonneg_left (by linarith) hε
      _ = δ := div_mul_cancel₀ δ hVp.ne'
  apply mul_le_mul_of_nonneg_right _ hlong
  exact (mul_le_mul_of_nonneg_left
    (allocatedSelectedNaturalWindowVolume_le_early B α O U b S selected) hε).trans heV

end Erdos3.VectorPolynomial

end

end OAI
