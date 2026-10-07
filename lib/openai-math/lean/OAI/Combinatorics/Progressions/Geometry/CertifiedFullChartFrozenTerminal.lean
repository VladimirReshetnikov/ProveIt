/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.DenseCommonStrideCardRatio
import OAI.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
import OAI.Combinatorics.Progressions.Lattices.AllocatedRecoveredIntegerFullChart
import OAI.Combinatorics.Progressions.Lattices.IntegerFrozenChart
import OAI.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterBox_coordinate_bound (t : integerBox sides)
    (k : LayerSamplerVariables G I n B) : |(t.val k : ℝ)| ≤ S.value := by
  have ht := (mem_integerBox sides t.val).mp t.property k
  have hside : sides k ≤ S.value := by
    cases k with
    | inl g => exact le_rfl
    | inr j => exact allocatedPrincipalSides_le_scale B U b S j
  have ht0 : (0 : ℝ) ≤ t.val k := by exact_mod_cast ht.1
  rw [abs_of_nonneg ht0]
  exact (by exact_mod_cast ht.2.le : (t.val k : ℝ) ≤ sides k).trans (Nat.cast_le.mpr hside)

theorem allocatedParameterBox_root_bound (t : integerBox sides) :
    (∑ k, |(t.val k : ℝ)|) ≤ allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    allocatedParameterBox_coordinate_bound B U b S t k)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, mul_zero, zero_add] using hsum

theorem allocatedParameterBox_slice_cost {p : ℝ} {A : Finset (integerBox sides)}
    (hA : IsDenseCommonStrideBox sides p (A.image Subtype.val)) :
    (Fintype.card (integerBox sides) : ℝ) / A.card ≤
      Real.exp (p * Fintype.card (LayerSamplerVariables G I n B)) := by
  exact dense_commonStride_slice_card_ratio Subtype.val Subtype.val_injective
    (by ext t; simp) hA

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterBox_side_eq (i : LayerSamplerVariables G I n B) :
    layerSamplerBox B U b S i = (sides i : ℝ) := by
  cases i <;> rfl

theorem allocatedFrozenParameterBox_mem
    (keep : LayerSamplerVariables G I n B → Prop) [DecidablePred keep]
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < sides i.val)
    (u : {i // keep i} → ℤ)
    (hu : u ∈ integerBox (fun i : {i // keep i} => sides i.val)) :
    finiteSplitPoint keep u fixed ∈ integerBox sides := by
  apply (mem_integerBox sides _).mpr
  intro i
  by_cases hi : keep i
  · simpa only [finiteSplitPoint, dite_eq_left hi] using
      (mem_integerBox _ u).mp hu ⟨i, hi⟩
  · simpa only [finiteSplitPoint, dite_eq_right hi] using hfixed ⟨i, hi⟩

theorem allocatedFrozenParameterBox_bound
    (keep : LayerSamplerVariables G I n B → Prop) [DecidablePred keep]
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < sides i.val)
    (u : {i // keep i} → ℤ)
    (hu : u ∈ integerBox (fun i : {i // keep i} => sides i.val)) :
    ∀ i, |((finiteSplitPoint keep u fixed i : ℤ) : ℝ)| ≤ layerSamplerBox B U b S i := by
  intro i
  have hi := (mem_integerBox sides _).mp
    (allocatedFrozenParameterBox_mem B U b S keep fixed hfixed u hu) i
  have hnonneg : (0 : ℝ) ≤ (finiteSplitPoint keep u fixed i : ℤ) := by exact_mod_cast hi.1
  rw [abs_of_nonneg hnonneg, allocatedParameterBox_side_eq B U b S]
  exact_mod_cast hi.2.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
local notation "Vars" => LayerSamplerVariables G I n B
local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterBox_physical_input
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1/2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    {k : ℕ} (hk : 2 ≤ k)
    (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k)
    (hinj : Function.Injective (fun t : integerBox sides =>
      jointIntegerPhysicalSite t.val (z.1.val,z.2.val))) :
    (∀ t ∈ integerBox sides,
      jointIntegerPhysicalSite t (z.1.val,z.2.val) ∈ integerBox N) ∧
    (∀ t ∈ integerBox sides,
      f (jointIntegerPhysicalSite t (z.1.val,z.2.val)) ∈ Set.Icc (0 : ℝ) 1) ∧
    IntegerVectorAPFree {t | t ∈ integerBox sides ∧
      f (jointIntegerPhysicalSite t (z.1.val,z.2.val)) ≠ 0} k := by
  have hinside (t : Vars → ℤ) (ht : t ∈ integerBox sides) :
      jointIntegerPhysicalSite t (z.1.val,z.2.val) ∈ integerBox N :=
    narrow_jointIntegerPhysicalSite_mem_box
      (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hτhalf hξ1 t
      (allocatedParameterBox_root_bound B U b S ⟨t,ht⟩) N hN hsize z
  refine ⟨hinside, fun t ht => hf _ (hinside t ht), ?_⟩
  have hset : Set.InjOn (fun t => jointIntegerPhysicalSite t (z.1.val,z.2.val))
      (integerBox sides : Set (Vars → ℤ)) := by
    intro u hu v hv huv
    exact congrArg Subtype.val (hinj (a₁ := ⟨u,hu⟩) (a₂ := ⟨v,hv⟩) huv)
  apply (joint_sample_progression_free hfree hk (z.1.val,z.2.val)
    (integerBox sides) hset).mono
  intro t ht
  exact ⟨ht.1, hinside t ht.1, ht.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_fullBox_normalized_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (hRootBudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x,
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let root : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    let hrootSum := fun t => (allocatedParameterBox_root_bound B U basis S t).trans hRootBudget
      let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S X p hm N hN _hW _hτ _hξ
        stride T hmass bases hbases hnormalizer.2.2.1
      let physical := narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        _hW _hτ _hξ1 N hN hmargin root hrootSum
      let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
      ∀ {Tests : (bases × rectangularWeightIndices 0 widths 1) → Type*}
        [∀ z, Nonempty (Tests z)]
        (slices : ∀ z, Tests z → Finset Sites) (tests : ∀ z, Tests z → Sites → ℂ)
        (w : X → ℕ) (degree : ℕ) {u pModel budget pSlice : ℝ}
        (_hu : 0 ≤ u) (_hpModel : 0 ≤ pModel) (_hbudget : 0 ≤ budget)
        (_hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
        (_hCtail : Ctail ≤ Real.exp pModel)
        (_hDense : ∀ z j, IsDenseCommonStrideBox sides pSlice ((slices z j).image root))
        (_htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
        {periodCap coverCap : ℝ} {lip : ℝ≥0},
        let K := Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
        u + 2 * pModel + budget + 30 ≤ E →
        (∀ signal : (X → ℤ) → ℂ, (∀ t, ‖signal t‖ ≤ 1) →
          (∀ t, t ∉ integerBox N → signal t = 0) →
          allocatedModelUnitThreshold u pModel K Ctail ≤ sampledSliceSeminorm pathLaw
            (fun z t => jointIntegerPhysicalSite (root t) (z.1.val, z.2.val)) slices tests signal →
          ∃ (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
            (F : integerBox N → ℂ),
            Nonempty (NativeSampleModel w degree budget (fun t : integerBox N => t.val) F) ∧
            Real.exp (-budget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
              (fun t => signal t.val) (fun t => star (twist.eval N p t.val) * F t)‖) →
        ∀ (input : integerBox N → ℂ), (∀ t, ‖input t‖ ≤ Real.exp pModel) →
        ∃ (nterms : ℕ) (_ : 0 < nterms)
          (Q : Fin nterms → (integerBox N → ℂ))
          (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
          (∀ i, Q i ∈ twistedNativeSampleFunctions w degree budget
            (fun t : integerBox N => t.val)
            (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
              (t : integerBox N) => twist.eval N p t.val)) ∧
          input = (∑ i, coeff i • Q i) + err ∧
          (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
          sampledSliceSeminorm pathLaw physical slices tests err ≤ Real.exp (-u) ∧
          (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * pModel + 30) := by
  obtain ⟨A, hA, hmodel⟩ := exists_allocated_narrow_normalized_approximation m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ _ I _ _ n B _ _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hRootBudget hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hmodel⟩ :=
    hmodel B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
      hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize hrank hRank T hT
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro sides Sites root hrootSum pathLaw physical Ctail Tests _ slices tests
    w degree u pModel budget pSlice hu hpModel hbudget hSliceLog hCtail hDense htests
    periodCap coverCap lip K htail hdetect input hinput
  have hsides (k : LayerSamplerVariables G I n B) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U basis S j
  let : ∀ k, NeZero (sides k) := fun k => ⟨(hsides k).ne'⟩
  let : Nonempty Sites := (integerBox_nonempty sides).to_subtype
  have hroot (t : Sites) (k) : |(root t k : ℝ)| ≤ Real.exp P :=
    (allocatedParameterBox_coordinate_bound B U basis S t k).trans hLP
  have hsizeModel (z) (j) : (Fintype.card Sites : ℝ) / (slices z j).card ≤ K :=
    allocatedParameterBox_slice_cost B U basis S (hDense z j)
  exact hmodel root hroot hrootSum slices tests w degree hu hpModel hbudget
    (Real.exp_nonneg _) (Real.exp_le_exp.mpr hSliceLog) hCtail hsizeModel htests
    htail hdetect input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators Classical

theorem integerSampledRealChart_freeze {A V : Type*}
    (β : A → MvPolynomial V ℤ) (keep : V → Prop)
    (fixed : {i // ¬keep i} → ℤ) (i : A) :
    integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) i =
      freezePolynomial keep (fun i => (fixed i : ℝ)) (integerSampledRealChart β i) :=
  freezePolynomial_map (Int.castRingHom ℝ) keep fixed (β i)

theorem integerSampledSpatial_freeze {m : ℕ} {X V : Type*} {J : Fin m → Type*}
    (β : X ⊕ (Σ j, J j) → MvPolynomial V ℤ) (keep : V → Prop)
    (fixed : {i // ¬keep i} → ℤ) (u : {i // keep i} → ℤ) :
    integerSampledSpatial (fun z => freezePolynomial keep fixed (β z)) u =
      integerSampledSpatial β (finiteSplitPoint keep u fixed) := by
  funext i
  exact freezePolynomial_eval keep fixed (β (Sum.inl i)) u

theorem integerSampledLowTags_freeze {m : ℕ} {X V : Type*}
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial V ℤ) (keep : V → Prop)
    (fixed : {i // ¬keep i} → ℤ) (u : {i // keep i} → ℤ) :
    integerSampledLowTags J k (fun z => freezePolynomial keep fixed (β z)) u =
      integerSampledLowTags J k β (finiteSplitPoint keep u fixed) := by
  funext i
  exact freezePolynomial_eval keep fixed (β (Sum.inr (lowTaggedIndex J k i))) u

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

noncomputable def allocatedFrozenIntegerFullChart
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ) :
    X ⊕ (Σ j, J j) → MvPolynomial {i // keep i} ℤ :=
  fun z => freezePolynomial keep fixed
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)

theorem allocatedFrozenIntegerFullChart_support
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ) :
    ∀ i, integerSampledRealChart
      (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) i ∈
      weightedSupportLE (fun _ : {i // keep i} => 1) (fullTaggedVariableWeight J i) := by
  intro i
  change integerSampledRealChart (fun z => freezePolynomial keep fixed
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i ∈ _
  rw [integerSampledRealChart_freeze]
  exact freezePolynomial_support keep _
    (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample i)

theorem allocatedFrozenIntegerFullChart_spatial
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (u : {i // keep i} → ℤ) :
    integerSampledSpatial
      (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u =
      jointIntegerPhysicalSite (finiteSplitPoint keep u fixed) (a, v) := by
  change integerSampledSpatial (fun z => freezePolynomial keep fixed
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) u = _
  rw [integerSampledSpatial_freeze, allocatedRecoveredIntegerFullChart_spatial]

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_low_residual
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val)
    (k : ℕ) (u : {i // keep i} → ℤ)
    (hu : u ∈ integerBox (fun i : {i // keep i} =>
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val))
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval
      (fun z => (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u z : ℝ))
      (lowTaggedPolynomial J k poly i) - (c (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u i : ℝ)| ≤ 1 / 8 := by
  have hs := integerSampledSpatial_freeze
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) keep fixed u
  have ht := integerSampledLowTags_freeze J k
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) keep fixed u
  change integerSampledSpatial
    (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u = _ at hs
  change integerSampledLowTags J k
    (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u = _ at ht
  rw [hs, ht]
  exact h.integerFullChart_low_residual B U b hb o S hR hσ poly hm hσ1 C hC hchart hsmall hp
    c a v sample read k (finiteSplitPoint keep u fixed)
    (allocatedFrozenParameterBox_bound B U b S keep fixed hfixed u hu) i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module Submodule VectorPolynomial
open scoped TensorProduct

variable {A V L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartLie weightedAdaptedRealChartHom

theorem weightedAdaptedRealChartHom_integer_freeze
    (w : A → ℕ) (β : A → MvPolynomial V ℤ)
    (keep : V → Prop) (fixed : {i // ¬keep i} → ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE (fun _ : V => 1) (w i))
    (hfreeze : ∀ i, integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) i ∈
      weightedSupportLE (fun _ : {i // keep i} => 1) (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
      (integerSampledRealChart (fun z => freezePolynomial keep fixed (β z))) hfreeze g =
      F.weightedAdaptedRealChartHom (fun _ : V => 1) (fun _ : {i // keep i} => 1)
        (frozenCoordinate keep (fun i => (fixed i : ℝ)))
        (frozenCoordinate_support keep (fun i => (fixed i : ℝ)))
        (F.weightedAdaptedRealChartHom w (fun _ : V => 1) (integerSampledRealChart β) hβ g) := by
  have hchart : integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) =
      fun i => MvPolynomial.aeval (frozenCoordinate keep (fun j => (fixed j : ℝ)))
        (integerSampledRealChart β i) := by
    funext i
    exact integerSampledRealChart_freeze β keep fixed i
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [weightedAdaptedRealChartHom_coord]
  rw [hchart]
  exact (realChartSubstitute_comp (integerSampledRealChart β)
    (frozenCoordinate keep (fun i => (fixed i : ℝ))) _).symm

variable {m : ℕ} {G X : Type*} [Fintype G] {I J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem weightedAdaptedRealChartHom_allocatedFrozenIntegerFullChart
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group) :
    F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i // keep i} => 1)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed))
      (allocatedFrozenIntegerFullChart_support B U b o poly hm c a v sample keep fixed) g =
      F.weightedAdaptedRealChartHom (fun _ : LayerSamplerVariables G I n B => 1)
        (fun _ : {i // keep i} => 1)
        (frozenCoordinate keep (fun i => (fixed i : ℝ)))
        (frozenCoordinate_support keep (fun i => (fixed i : ℝ)))
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : LayerSamplerVariables G I n B => 1)
          (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
          (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample) g) := by
  exact F.weightedAdaptedRealChartHom_integer_freeze (fullTaggedVariableWeight J)
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) keep fixed
    (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample)
    (allocatedFrozenIntegerFullChart_support B U b o poly hm c a v sample keep fixed) g

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {G X ι η L : Type} [Fintype G] [Fintype η]
  [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
  (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Kinitial : Set (X ⊕ (Σ j, J j) → ℝ)} {N : X → ℕ} {Bphase : ℝ}

theorem allocatedFrozen_terminal_mem_fast
    (history : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift
      Z Kinitial Utag poly N Bphase s)
    (hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
    (c : ∀ j, Utag j) (origin : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g = Z)
    (htop : ∀ u : {i // keep i} → ℝ,
      (fun z => MvPolynomial.eval u (homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart
          (allocatedFrozenIntegerFullChart B Utag btag otag poly hm
            c origin v sample keep fixed) z))) ∈ history.K) :
    let β := allocatedFrozenIntegerFullChart B Utag btag otag poly hm
      c origin v sample keep fixed
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (fun z => homogeneousComponent (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
      (fun z => sampledTopPhase_coordinate_homogeneous
        (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
    ∀ u : {i // keep i} → ℝ,
      eval₂ u (F.realGradedSymbolPolynomial b ω hF (fun _ : {i // keep i} => 1)
        ((pull history.outer.1)⁻¹ *
          F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
            (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
              (fun _ : {i // keep i} => 1) (integerSampledRealChart β)
              (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm
                c origin v sample keep fixed) g) *
          (pull history.outer.2)⁻¹).coord) ∈ fast.baseChange ℝ := by
  intro β pull u
  have hactual : F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : {i // keep i} => 1) (integerSampledRealChart β)
        (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm
          c origin v sample keep fixed) g) = pull Z := by
    rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart b ω hF
      (fullTaggedVariableWeight J) (fun _ : {i // keep i} => 1)
      (integerSampledRealChart β)
      (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm
        c origin v sample keep fixed) g, hZ]
    rfl
  rw [hactual, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
  simp only [pull, F.realSymbolHomogeneousPullbackHom_coord]
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF
    (fullTaggedVariableWeight J) (fun _ : {i // keep i} => 1)
    (fun z => homogeneousComponent (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
    (fun z => sampledTopPhase_coordinate_homogeneous
      (fullTaggedVariableWeight J z) (integerSampledRealChart β z)), eval₂_realChartSubstitute]
  exact history.terminal_mem_fast hfast _ (htop u)

theorem allocatedFrozen_terminal_mem_symbolPointwiseSubalgebra
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    {basisW : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule))}
    {liftW : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded}
    (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basisW liftW
      Z Kinitial Utag poly N Bphase s)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (c : ∀ j, Utag j) (origin : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g = Z)
    (htop : ∀ u : {i // keep i} → ℝ,
      (fun z => MvPolynomial.eval u (homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart
          (allocatedFrozenIntegerFullChart B Utag btag otag poly hm
            c origin v sample keep fixed) z))) ∈ history.K) :
    let β := allocatedFrozenIntegerFullChart B Utag btag otag poly hm
      c origin v sample keep fixed
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (fun z => homogeneousComponent (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
      (fun z => sampledTopPhase_coordinate_homogeneous
        (fullTaggedVariableWeight J z) (integerSampledRealChart β z))
    ((pull history.outer.1)⁻¹ *
      F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : {i // keep i} => 1) (integerSampledRealChart β)
          (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm
            c origin v sample keep fixed) g) *
      (pull history.outer.2)⁻¹).coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i // keep i} => 1) W) := by
  intro β pull
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
    (fun _ : {i // keep i} => 1) W _).mpr
  exact history.allocatedFrozen_terminal_mem_fast B Utag btag otag poly hm hW
    c origin v sample keep fixed g hZ htop

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI
