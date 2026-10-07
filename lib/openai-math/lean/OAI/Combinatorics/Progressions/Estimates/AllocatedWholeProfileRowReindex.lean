import OAI.Combinatorics.Progressions.Probability.AllocatedNormalizedConditionalHaar

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O O' : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]
variable (e : ∀ j, O' j ≃ O j)
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

omit [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] in
theorem allocatedNonkernelJetMatrix_reindex_rows
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (j : Fin m) :
    allocatedNonkernelJetMatrix B U b S x u (fun j => rows j ∘ e j) j v =
      (allocatedNonkernelJetMatrix B U b S x u rows j v).submatrix (e j) id := rfl

omit [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] in
theorem allocatedIntegerKernelMask_reindex_rows (q : ℕ) (j : Fin m)
    (r : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod q)) (z : O j → ℤ) :
    allocatedIntegerKernelMask B U b S x (fun j => rows j ∘ e j) j q
      (r.submatrix (e j) id) (z ∘ e j) = allocatedIntegerKernelMask B U b S x rows j q r z :=
  coefficientResidueMultiplier_reindex_rows (e j) (scalarKernelIntegerJet x (j.val+1) (rows j)) r z

include e in
theorem allocatedLongJetOutputScale_reindex_rows (a : {a // ¬grid a}) :
    allocatedLongJetOutputScale B U b S (O := O') a =
      allocatedLongJetOutputScale B U b S (O := O) a := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · rfl
  · exact congrArg (fun k => (basisAxisScale (b j) i : ℝ)^k) (Fintype.card_congr (e j))

omit [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] in
theorem allocatedLongJetMask_reindex_rows (q : ℕ)
    (r : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod q))
    (a : {a // ¬grid a}) (z : CoefficientJetAxisRow O a.val) :
    allocatedLongJetMask B U b S x (fun j => rows j ∘ e j) q
      (fun j => (r j).submatrix (e j) id) a (coefficientJetRowReindex e a.val z) =
      allocatedLongJetMask B U b S x rows q r a z := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · rfl
  · exact allocatedIntegerKernelMask_reindex_rows B U b S e x rows q j (r j) z

omit [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] in
theorem allocatedLongJetRealCoordinates_reindex_rows (z : AllocatedLongJetRows B U b S O) :
    allocatedLongJetRealCoordinates B U b S (coefficientJetRowsReindex e (fun a => ¬grid a) z) =
      fun p => allocatedLongJetRealCoordinates B U b S z ⟨p.1, e p.1.val.1 p.2⟩ := by
  funext p
  rcases p with ⟨⟨⟨j, i | i⟩, ha⟩, t⟩ <;> rfl

theorem allocatedLongProfileDensity_reindex_rows (q : ℕ)
    (r : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod q))
    (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ)
    (z : AllocatedLongJetRows B U b S O) :
    allocatedLongProfileDensity B U b S x (fun j => rows j ∘ e j) q
      (fun j => (r j).submatrix (e j) id)
      (fun v => f (fun p => v ⟨p.1, (e p.1.val.1).symm p.2⟩))
      (coefficientJetRowsReindex e (fun a => ¬grid a) z) =
      allocatedLongProfileDensity B U b S x rows q r f z := by
  unfold allocatedLongProfileDensity
  have hm : (∏ a : {a // ¬grid a}, allocatedLongJetMask B U b S x
      (fun j => rows j ∘ e j) q (fun j => (r j).submatrix (e j) id) a
        ((coefficientJetRowsReindex e (fun a => ¬grid a) z) a)) =
      ∏ a : {a // ¬grid a}, allocatedLongJetMask B U b S x rows q r a (z a) :=
    Finset.prod_congr rfl (fun a _ => allocatedLongJetMask_reindex_rows B U b S e x rows q r a (z a))
  rw [hm, allocatedLongJetRealCoordinates_reindex_rows B U b S e]
  simp only [Equiv.apply_symm_apply]
  congr 1
  exact Finset.prod_congr rfl (fun a _ => allocatedLongJetOutputScale_reindex_rows B U b S e a)

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
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O O' : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]
variable (e : ∀ j, O' j ≃ O j) (rows : ∀ j, O j → Finset α)
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedCoveredFixedFactor_reindex_rows (z : MixedCoveredJetSource I O Q n d) :
    allocatedCoveredFixedFactor B U b hR hσ S x u v (fun j => rows j ∘ e j) Q d
      (mixedCoveredRowsReindex e d z).1 (mixedCoveredRowsReindex e d z).2 =
      allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 := by
  unfold allocatedCoveredFixedFactor
  rw [coveredJetArrayScale_reindex_rows e U]
  have hd := coefficientDeckJetDensity_reindex_rows e root dirs rows d z.2
  change _ * coefficientDeckJetDensity root dirs (fun j => rows j ∘ e j) d
    (fun j t => z.2 j (e j t)) / _ = _
  rw [hd]
  congr 2
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact congrArg ENNReal.toReal (integerMatrixImagePMF_reindex_rows (e j)
      (boundedCoefficientJetMatrix root dirs (j.val+1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i) ((z.1 j).2 i))

omit [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] [∀ j, Fintype (Q j)] [NeZero d] in
theorem coefficientJetAxisSplit_long_reindex_rows (z : MixedCoveredJetSource I O Q n d) :
    (coefficientJetAxisSplit O' I n grid (mixedCoveredRowsReindex e d z).1).2 =
      coefficientJetRowsReindex e (fun a => ¬grid a) ((coefficientJetAxisSplit O I n grid z.1).2) := by
  funext a
  rcases a with ⟨⟨j, i | i⟩, ha⟩ <;> rfl

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

include hΩ in
theorem allocatedCoveredProfileDensity_reindex_rows
    (f : AllocatedLongJetRows B U b S O → ℝ)
    (f' : AllocatedLongJetRows B U b S O' → ℝ)
    (hf : ∀ z, f' (coefficientJetRowsReindex e (fun a => ¬grid a) z) = f z)
    (y : EuclideanJetLayers U O) :
    allocatedCoveredProfileDensity B U b hR hσ S x u v (fun j => rows j ∘ e j) hb o bW d
      (fun j => Ω j ∘ e j) f' (euclideanJetRowsReindex e U y) =
      allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω f y := by
  apply restrictedChartDensity_reindex (mixedCoveredRowsReindex e d) (euclideanJetRowsReindex e U).toEquiv
    _ _ _ _ 1 _ _
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
    (mixedCoveredJetChart_injOn U o b hb bW d (fun j => Ω j ∘ e j) (fun j t => hΩ j (e j t)))
    (mixedCoveredJetChart_reindex_rows e U o b hb bW d)
    (mixedCoveredJetRegion_reindex_rows e U o b d Ω)
  intro z
  rw [allocatedCoveredFixedFactor_reindex_rows B U b hR hσ S x u v e rows d,
    coefficientJetAxisSplit_long_reindex_rows B U b S e d, hf]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O O' : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]
variable (e : ∀ j, O' j ≃ O j) (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedWholeMaskedCoveredProfile_reindex_rows
    (w : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ)
    (y : EuclideanJetLayers U O) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x (fun j => rows j ∘ e j) hb o bW d w q
      (fun z => f (fun p => z ⟨p.1, (e p.1.val.1).symm p.2⟩)) (euclideanJetRowsReindex e U y) =
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d w q f y := by
  apply allocatedCoveredProfileDensity_reindex_rows B U b hR hσ S x
    (principalAxisRestrict grid w) (principalAxisRestrict (fun a => ¬grid a) w) e rows d hb o bW
    (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  intro z
  exact allocatedLongProfileDensity_reindex_rows B U b S e x rows q
    (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict grid w) rows j (principalAxisRestrict (fun a => ¬grid a) w)) q) f z

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, SigmaFinite (ν j)]

theorem allocatedWholeMaskedCoveredProfile_reindex_integral
    (w : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ)
    (F : EuclideanJetLayers U O' → ℂ) :
    (∫ y, (allocatedWholeMaskedCoveredProfile B U b hR hσ S x (fun j => rows j ∘ e j) hb o bW d w q
      (fun z => f (fun p => z ⟨p.1, (e p.1.val.1).symm p.2⟩)) y : ℂ) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : O' j => ν j))) =
      ∫ y, (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d w q f y : ℂ) *
        F (euclideanJetRowsReindex e U y) ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)) := by
  rw [← (euclideanJetRowsReindex_measurePreserving e U ν).integral_comp
    (euclideanJetRowsReindex e U).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [allocatedWholeMaskedCoveredProfile_reindex_rows B U b hR hσ S x e rows hb o bW d w q f y]

theorem allocatedWholeMaskedCoveredProfile_reindex_mean_integral
    {A : Type*} [Fintype A] (p : FiniteProbabilityWeights A)
    (w : A → PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ)
    (F : EuclideanJetLayers U O' → ℂ) :
    (∫ y, (p.mean (fun a => allocatedWholeMaskedCoveredProfile B U b hR hσ S x
      (fun j => rows j ∘ e j) hb o bW d (w a) q
      (fun z => f (fun p => z ⟨p.1, (e p.1.val.1).symm p.2⟩)) y) : ℂ) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : O' j => ν j))) =
      ∫ y, (p.mean (fun a => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (w a) q f y) : ℂ) * F (euclideanJetRowsReindex e U y)
          ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)) := by
  rw [← (euclideanJetRowsReindex_measurePreserving e U ν).integral_comp
    (euclideanJetRowsReindex e U).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with y
  simp_rw [allocatedWholeMaskedCoveredProfile_reindex_rows B U b hR hσ S x e rows hb o bW d]

end Erdos3.VectorPolynomial

end

end OAI
