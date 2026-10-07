import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedProductPrefactorCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

local notation "Output" => (Σ _e : OneCubeActiveRow grid, Unit)

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedSlicedPhysicalJetIdeal_coordinate_support
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (z : Jet → ℝ) (hz : allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z ≠ 0)
    (a₀ : {a // ¬grid a}) (t : Finset (Fin 1)) :
    |z ⟨a₀,t⟩| ≤ 4 * R a₀.val.1 := by
  let e := oneCubeJetEndpointEquiv {a // ¬grid a}
  let w : Output → ℝ := fun o => e z o / R o.1.2.val.1
  have hw0 : allocatedSlicedAveragedIdealDensity B U basis S hB lower width w ≠ 0 := by
    intro he
    apply hz
    unfold allocatedSlicedPhysicalJetIdeal allocatedSlicedPhysicalEndpointIdeal
    rw [diagonalDensityTransport_eq, oneCubeJointJetEndpoints_equiv]
    change |∏ o : Output, R o.1.2.val.1|⁻¹ * allocatedSlicedAveragedIdealDensity B U basis S hB lower width w = 0
    rw [he, mul_zero]
  have hw2 : ‖w‖ ≤ 2 := le_of_not_gt (fun h => hw0
    (allocatedSlicedAveragedIdealDensity_zero_off_ball B U basis S hB lower width hwidth ha hδ hprincipal hw hl w h))
  have hend (β : Bool) : |e z ⟨(β,a₀),()⟩| ≤ 2 * R a₀.val.1 := by
    have he := (norm_le_pi_norm w (⟨(β,a₀),()⟩ : Output)).trans hw2
    change ‖e z ⟨(β,a₀),()⟩ / R a₀.val.1‖ ≤ 2 at he
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hR _)] at he
    exact (div_le_iff₀ (hR _)).mp he
  have h₀ := hend false
  have h₁ := hend true
  simp only [e, oneCubeJetEndpointEquiv_apply, Bool.false_eq_true, ↓reduceIte] at h₀ h₁
  fin_cases t
  · change |z ⟨a₀,∅⟩| ≤ _
    linarith only [h₀, hR a₀.val.1]
  · change |z ⟨a₀,{0}⟩| ≤ _
    have hsub : |z ⟨a₀,{0}⟩| ≤ |z ⟨a₀,∅⟩ + z ⟨a₀,{0}⟩| + |z ⟨a₀,∅⟩| := by
      have h := abs_sub_le (z ⟨a₀,∅⟩ + z ⟨a₀,{0}⟩) 0 (z ⟨a₀,∅⟩)
      simpa only [add_sub_cancel_left, sub_zero, zero_sub, abs_neg] using h
    linarith only [h₀, h₁, hsub]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "rawRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v rows

theorem allocatedFrozenProfile_mixed_integral
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f)
    (hf : Integrable f longRef)
    (φ : (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) → ℂ)
    (hφ : Measurable φ) {C : ℝ} (hbound : ∀ z, ‖φ z‖ ≤ C) :
    (∫ a, ∫ z, (f z : ℂ) * φ (allocatedMixedJetReconstruct B U b S x u v rows a z)
      ∂longRef ∂allocatedFrozenCoefficientSource B U b hR hσ S) =
    ∫ z, ((fg ((split z).1) * f ((split z).2) : ℝ) : ℂ) * φ z ∂rawRef := by
  let ψ := fun p : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O =>
    (f p.2 : ℂ) * φ ((split).symm p)
  have hψ : Measurable ψ :=
    (Complex.measurable_ofReal.comp (hfm.comp measurable_snd)).mul
      (hφ.comp (split).symm.measurable)
  have hint : Measurable (fun g => ∫ z, ψ (g, z) ∂longRef) :=
    hψ.stronglyMeasurable.integral_prod_right'.measurable
  have hfg := (allocatedGridJetDensity_probability_data B U b S O hR hσ x u v rows).1
  have hprod : Integrable (fun p : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O =>
      ((fg p.1 * f p.2 : ℝ) : ℂ) * φ ((split).symm p)) ((gridRef).prod longRef) :=
    (hfg.mul_prod hf).ofReal.mul_bdd (hφ.comp (split).symm.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound _))
  calc
    _ = ∫ g, (fg g : ℂ) * (∫ z, ψ (g, z) ∂longRef) ∂gridRef := by
      change (∫ a, (fun g => ∫ z, ψ (g, z) ∂longRef)
        (allocatedFrozenJetMap B U b S x u v rows a)
        ∂allocatedFrozenCoefficientSource B U b hR hσ S) = _
      rw [← integral_map (allocatedFrozenJetMap_measurable B U b S x u v rows).aemeasurable
        hint.aestronglyMeasurable, allocatedGridJetDensity_law B U b S O hR hσ x u v rows,
        realDensityMeasure_integral_complex gridRef fg
          (allocatedGridJetDensity_measurable B U b hR hσ S x u v rows)
          (fun z => (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows z).1)]
    _ = ∫ g, ∫ z, ((fg g * f z : ℝ) : ℂ) * φ ((split).symm (g, z)) ∂longRef ∂gridRef := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun g => by
        calc
          _ = ∫ z, (fg g : ℂ) * ψ (g, z) ∂longRef :=
            (integral_const_mul (fg g : ℂ) (fun z => ψ (g, z))).symm
          _ = _ := integral_congr_ae (Filter.Eventually.of_forall
            (fun z => by simp only [ψ, Complex.ofReal_mul, mul_assoc])))
    _ = ∫ p, ((fg p.1 * f p.2 : ℝ) : ℂ) * φ ((split).symm p) ∂(gridRef).prod longRef :=
      (integral_prod _ hprod).symm
    _ = _ := by
      have he := coefficientJetAxisSplit_measurePreserving O I n grid
      have hh := he.integral_comp (split).measurableEmbedding
        (fun p => ((fg p.1 * f p.2 : ℝ) : ℂ) * φ ((split).symm p))
      simpa only [allocatedFrozenJetReference, allocatedLongJetReference,
        MeasurableEquiv.symm_apply_apply] using hh.symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "mixedRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v₀ rows
local notation "fd" => coefficientDeckJetDensity (B := Q) root dirs rows d
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

omit [Fintype α] in
theorem allocatedCoveredDeck_density_test
    (F : EuclideanJetLayers U O → ℂ)
    (t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    (∫ r, F (chart (t, coefficientDeckJetMap root dirs rows d r)) ∂(deck).toMeasure) =
      ∫ r, (fd r : ℂ) * F (chart (t, r))
        ∂(PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure := by
  have he := coefficientDeckJetDensity_integral
    (K := LayerSamplerVariables G I n B) (O := O) (B := Q)
    root dirs rows d (fun r => F (chart (t, r)))
  convert he using 1
  apply congrArg (fun p : PMF (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d) =>
    ∫ r, F (chart (t, coefficientDeckJetMap root dirs rows d r)) ∂p.toMeasure)
  exact congrArg (fun i : Fintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d) =>
    @PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d) i _)
      (Subsingleton.elim _ _)

omit [Fintype α] in
theorem allocatedCoveredProfile_raw_integral
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f)
    (hf : Integrable f longRef)
    (F : EuclideanJetLayers U O → ℂ) (hF : Measurable F)
    {C : ℝ} (hbound : ∀ z, ‖F z‖ ≤ C) :
    (∫ a, ∫ z, (f z : ℂ) *
      allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d (fun p => F p.2) a z
      ∂longRef ∂allocatedFrozenCoefficientSource B U b hR hσ S) =
    ∫ z, (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z : ℂ) *
      F (chart z) ∂raw := by
  let φ := fun t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ) =>
    ∫ r, F (chart (t, coefficientDeckJetMap root dirs rows d r)) ∂(deck).toMeasure
  have hchart : Measurable chart :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  have hφ : Measurable φ := finitePMF_integral_measurable deck _
    (fun r => hF.comp (hchart.comp (measurable_id.prodMk measurable_const)))
  have hφb : ∀ t, ‖φ t‖ ≤ C := fun t => finitePMF_integral_norm_le deck _ (fun r => hbound _)
  have hφeq (t) : φ t = ∫ r, (fd r : ℂ) * F (chart (t, r)) ∂(PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure := by
    exact allocatedCoveredDeck_density_test B U b S x u v₀ rows Q hb o bW d F t
  have hi := (allocatedGridlessWeightedKernel_mass_data B U b S x u v₀ rows (Q := Q) d fg f
    (allocatedGridJetDensity_probability_data B U b S O hR hσ x u v₀ rows).1 hf).1
  have hprod : Integrable (fun z : MixedCoveredJetSource I O Q n d =>
      (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z : ℂ) *
        F (chart z)) raw :=
    hi.ofReal.mul_bdd (hF.comp hchart).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => hbound _))
  calc
    _ = ∫ t, ((fg ((split t).1) * f ((split t).2) : ℝ) : ℂ) * φ t ∂mixedRef :=
      allocatedFrozenProfile_mixed_integral B U b S O hR hσ x u v₀ rows f hfm hf φ hφ hφb
    _ = ∫ t, ∫ r,
        (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f (t, r) : ℂ) *
          F (chart (t, r)) ∂(PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure ∂mixedRef := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      change ((fg ((split t).1) * f ((split t).2) : ℝ) : ℂ) * φ t = _
      rw [hφeq t]
      rw [← integral_const_mul (((fg ((split t).1) * f ((split t).2) : ℝ) : ℂ))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by
        simp only [allocatedGridlessWeightedKernel, Complex.ofReal_mul, mul_assoc])
    _ = _ := (integral_prod _ hprod).symm

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

omit [Fintype α] in
include hΩm hΩ in
theorem allocatedCoveredProfile_test_integral
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f)
    (hf : Integrable f longRef) (hf0 : ∀ z, 0 ≤ f z)
    (hfs : ∀ z ∉ mixedCoveredJetRegion (E := Q) U o b d Ω,
      allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z = 0)
    (F : EuclideanJetLayers U O → ℂ) (hF : Measurable F)
    {C : ℝ} (hbound : ∀ z, ‖F z‖ ≤ C) :
    (∫ a, ∫ z, (f z : ℂ) *
      allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d (fun p => F p.2) a z
      ∂longRef ∂allocatedFrozenCoefficientSource B U b hR hσ S) =
    ∫ y, (allocatedCoveredProfileDensity B U b hR hσ S x u v₀ rows hb o bW d Ω f y : ℂ) *
      F y ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)) := by
  rw [allocatedCoveredProfile_raw_integral B U b hR hσ S x u v₀ rows Q hb o bW d f hfm hf F hF hbound]
  have hm := allocatedGridlessWeightedKernel_measurable B U b S x u v₀ rows (Q := Q) d fg f
    (allocatedGridJetDensity_measurable B U b hR hσ S x u v₀ rows) hfm
  have h0 (z : MixedCoveredJetSource I O Q n d) :
      0 ≤ allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z :=
    mul_nonneg (mul_nonneg
      (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v₀ rows _).1 (hf0 _))
      (coefficientDeckJetDensity_nonneg root dirs rows d _)
  have he := mixedCoveredJet_normalized_complex_integral U o b hb bW d ν Ω hΩm hΩ _ hm h0 hfs F hF
  have hid : (fun z : MixedCoveredJetSource I O Q n d =>
      allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z /
        coveredJetArrayScale (O := O) U) =
      (fun z => allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z.1 z.2 * f ((split z.1).2)) := by
    funext z
    change fg ((split z.1).1) * f ((split z.1).2) * fd z.2 / coveredJetArrayScale (O := O) U =
      (fg ((split z.1).1) * fd z.2 / coveredJetArrayScale (O := O) U) * f ((split z.1).2)
    ring
  rw [hid] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "mixedRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v₀ rows
local notation "fd" => coefficientDeckJetDensity (B := Q) root dirs rows d
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

theorem allocatedGridlessWeightedKernel_quarter_support
    (hσ1 : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (f : AllocatedLongJetRows B U b S O → ℝ)
    (hs : ∀ z, f z ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : O a.val.1,
      |allocatedLongJetRealCoordinates B U b S z ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (z : MixedCoveredJetSource I O Q n d)
    (hz : allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z ≠ 0) :
    z ∈ mixedCoveredJetRegion (E := Q) U o b d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)) := by
  have hmul : fg ((split z.1).1) * f ((split z.1).2) ≠ 0 :=
    (mul_ne_zero_iff.mp hz).1
  have hg := (mul_ne_zero_iff.mp hmul).1
  have hl := hs _ (mul_ne_zero_iff.mp hmul).2
  have hr (j : Fin m) (t : O j) (i : I j) : |(z.1 j).1 i t| ≤ T j * R j :=
    hl ⟨⟨j, Sum.inl i⟩, by change ¬False; exact not_false⟩ t
  have hi (j : Fin m) (t : O j) (i : Fin (n j)) :
      |((z.1 j).2 i t : ℝ) / basisAxisScale (b j) i| ≤ T j * R j := by
    by_cases ha : grid ⟨j, Sum.inr i⟩
    · exact (allocatedGridJetDensity_scaled_support_bound B U b hR hσ S x u v₀ rows z.1 hg j
        (hσ1 j) i ha t).trans (mul_le_mul_of_nonneg_right (hsource j) (hR j).le)
    · exact hl ⟨⟨j, Sum.inr i⟩, ha⟩ t
  intro j _ t _
  refine ⟨?_, Set.mem_univ _⟩
  intro i
  have hn : ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d z j t).1‖ ≤ 1 / 4 :=
    (mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
      (mul_nonneg (hT j) (hR j).le) (hchart j) _ _ (hr j t) (hi j t)).trans (hbudget j)
  have hc : |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (mixedCoveredJetCoordinates U o d z j t).1 i| ≤
      ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (mixedCoveredJetCoordinates U o d z j t).1‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le
      (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (mixedCoveredJetCoordinates U o d z j t).1) i
  exact hc.trans hn

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

local notation "Output" => (Σ _e : OneCubeActiveRow grid, Unit)

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (v₀ : PrincipalAxisTuples (α := Fin 1) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))
local notation "ideal" => allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
local notation "reference" => allocatedLongJetReference B U basis S jetRows

theorem allocatedSlicedCoveredProfile_test_integral
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hRbound : ∀ j, R j ≤ Real.exp P) (hInv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (Finset (Fin 1)) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {Cmask : ℝ} (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x (fun _ => id) j modulus (residue j) z ≤ Cmask)
    (hσ1 : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 4 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (F : EuclideanJetLayers U jetRows → ℂ) (hF : Measurable F)
    {CF : ℝ} (hFb : ∀ z, ‖F z‖ ≤ CF) :
    let f := allocatedLongProfileDensity B U basis S x (fun _ => id) modulus residue ideal
    (∫ a₀, ∫ z, (f z : ℂ) * allocatedCoveredFixedTest B U basis S x u v₀ (fun _ => id)
      Q hb o bW d (fun p => F p.2) a₀ z ∂reference ∂allocatedFrozenCoefficientSource B U basis hR hσ S) =
      ∫ y, (allocatedCoveredProfileDensity B U basis hR hσ S x u v₀ (fun _ => id) hb o bW d
        (fun j (_ : Finset (Fin 1)) => standardLatticeClosedQuarterBox (J j)) f y : ℂ) * F y
          ∂Measure.pi (fun j => Measure.pi (fun _ : Finset (Fin 1) => ν j)) := by
  intro f
  have hfm : Measurable f := allocatedLongProfileDensity_measurable B U basis S x (fun _ => id)
    modulus residue ideal (allocatedSlicedPhysicalJetIdeal_measurable B U basis S hR hB lower width)
  have hfi : Integrable f reference := allocatedSlicedLongProfile_integrable B U basis S x hR hB lower width
    O hO hwidth ha hδ hP haP hδP hprincipal hw hl hRbound hInv modulus residue hCmask hmask
  have hf0 : ∀ z, 0 ≤ f z := allocatedLongProfileDensity_nonneg B U basis S x (fun _ => id)
    modulus residue ideal
      (allocatedSlicedPhysicalJetIdeal_probability B U basis S hR hB lower width ha hδ hprincipal hw hl).1
      (fun j z => (hmask j z).1)
  apply allocatedCoveredProfile_test_integral B U basis hR hσ S x u v₀ (fun _ => id) Q hb o bW d ν
    (fun j (_ : Finset (Fin 1)) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) f hfm hfi hf0 ?_ F hF hFb
  intro z hz
  by_contra hn
  apply hz
  apply allocatedGridlessWeightedKernel_quarter_support B U basis hR hσ S x u v₀ (fun _ => id) Q o d
    hσ1 T (fun j => le_trans (by norm_num) (hT j)) hsource C hC hchart hbudget f ?_ z hn
  intro w hwne a₀ t
  have hi := allocatedLongProfileDensity_ne_zero B U basis S x (fun _ => id) modulus residue ideal w hwne
  exact (allocatedSlicedPhysicalJetIdeal_coordinate_support B U basis S hR hB lower width
    hwidth ha hδ hprincipal hw hl _ hi a₀ t).trans
      (mul_le_mul_of_nonneg_right (hT _) (hR _).le)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

local notation "Output" => (Σ _e : OneCubeActiveRow grid, Unit)

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (v₀ : PrincipalAxisTuples (α := Fin 1) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))
local notation "ideal" => allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
local notation "reference" => allocatedLongJetReference B U basis S jetRows

theorem allocatedSlicedCoveredProfile_mean_test_integral
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hRbound : ∀ j, R j ≤ Real.exp P) (hInv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (modulus : ℕ)
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := Fin 1)
      (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)))
    (residue : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
      (allocatedPrincipalSides B U basis S) → ∀ j, Matrix (Finset (Fin 1)) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {Cmask : ℝ} (hCmask : 1 ≤ Cmask)
    (hmask : ∀ u j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j modulus (residue u j) z ∧
      allocatedIntegerKernelMask B U basis S x (fun _ => id) j modulus (residue u j) z ≤ Cmask)
    (hσ1 : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 4 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (F : EuclideanJetLayers U jetRows → ℂ) (hF : Measurable F)
    {CF : ℝ} (hFb : ∀ z, ‖F z‖ ≤ CF) :

    let f := fun u => allocatedLongProfileDensity B U basis S x (fun _ => id) modulus (residue u) ideal
    weights.complexMean (fun u => ∫ a₀, ∫ z, (f u z : ℂ) *
      allocatedCoveredFixedTest B U basis S x u v₀ (fun _ => id) Q hb o bW d
        (fun p => F p.2) a₀ z ∂reference ∂allocatedFrozenCoefficientSource B U basis hR hσ S) =
      ∫ y, (weights.mean (fun u => allocatedCoveredProfileDensity B U basis hR hσ S x u v₀ (fun _ => id)
        hb o bW d (fun j (_ : Finset (Fin 1)) => standardLatticeClosedQuarterBox (J j)) (f u) y) : ℂ) * F y
          ∂Measure.pi (fun j => Measure.pi (fun _ : Finset (Fin 1) => ν j)) := by
  intro f
  let profile := fun u => allocatedCoveredProfileDensity B U basis hR hσ S x u v₀ (fun _ => id)
    hb o bW d (fun j (_ : Finset (Fin 1)) => standardLatticeClosedQuarterBox (J j)) (f u)
  have hi u : Integrable (fun y => (profile u y : ℂ) * F y)
      (Measure.pi (fun j => Measure.pi (fun _ : Finset (Fin 1) => ν j))) := by
    have hfm : Measurable (f u) := allocatedLongProfileDensity_measurable B U basis S x (fun _ => id)
      modulus (residue u) ideal (allocatedSlicedPhysicalJetIdeal_measurable B U basis S hR hB lower width)
    have hfi : Integrable (f u) reference := allocatedSlicedLongProfile_integrable B U basis S x hR hB lower width
      O hO hwidth ha hδ hP haP hδP hprincipal hw hl hRbound hInv modulus (residue u) hCmask (hmask u)
    exact (allocatedCoveredProfileDensity_integrable B U basis hR hσ S x u v₀ (fun _ => id) hb o bW d
      (fun j (_ : Finset (Fin 1)) => standardLatticeClosedQuarterBox (J j))
      (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) ν (f u) hfm hfi).ofReal.mul_bdd
        hF.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
  calc
    _ = weights.complexMean (fun u => ∫ y, (profile u y : ℂ) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : Finset (Fin 1) => ν j))) := by
      apply congrArg weights.complexMean
      funext u
      exact allocatedSlicedCoveredProfile_test_integral B U basis S x u hR hB lower width hσ v₀ Q hb o bW d ν
        O hO hwidth ha hδ hP haP hδP hprincipal hw hl hRbound hInv modulus (residue u) hCmask (hmask u)
        hσ1 T hT hsource C hC hchart hbudget F hF hFb
    _ = ∫ y, weights.complexMean (fun u => (profile u y : ℂ) * F y)
        ∂Measure.pi (fun j => Measure.pi (fun _ : Finset (Fin 1) => ν j)) :=
      (weights.integral_complexMean _ _ hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => weights.complexMean_ofReal_mul _ _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)] [∀ j, DecidableEq (I j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable (hR : ∀ j, 0 < R j) (hrows : ∀ j t, t ∈ rowSets j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

omit [∀ index, DecidableEq (I index)] in
theorem allocatedSlicedRowIdeal_coordinate_support
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (z : (Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ)
    (hz : allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width z ≠ 0)
    (a₀ : {a // ¬grid a}) (t : rowTypes a₀.val.1) :
    |z ⟨a₀,t⟩| ≤ 4 * R a₀.val.1 :=
  allocatedSlicedPhysicalJetIdeal_coordinate_support B U b S hR hB lower width hwidth ha hδ
    hprincipal hw hl (fun q => z ⟨q.1, ⟨q.2, hrows q.1.val.1 q.2⟩⟩) hz a₀ t.val

end Erdos3.VectorPolynomial

end

end OAI
