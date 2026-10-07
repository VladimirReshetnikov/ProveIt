import Mathlib.Logic.Equiv.Option
import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess
import OAI.Combinatorics.Progressions.Estimates.SampledNativeDetectionEmptyTags
import OAI.Combinatorics.Progressions.Lattices.SelectedResidueScalarReindex

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

private theorem normalizedSliceTest_equiv
    {T T' : Type*} [Fintype T] [Fintype T']
    (e : T ≃ T') (S : Finset T) (w : T → ℂ) (t : T) :
    normalizedSliceTest (S.map e.toEmbedding) (fun u => w (e.symm u)) (e t) =
      normalizedSliceTest S w t := by
  simp [normalizedSliceTest, Fintype.card_congr e]

private theorem sampledSingleSliceSeminorm_equiv
    {T T' X : Type*} [Fintype T] [Fintype T']
    (e : T ≃ T') (F : T → X) (S : Finset T) (w : T → ℂ) :
    sampledSingleTestSeminorm (fun u => F (e.symm u))
      (normalizedSliceTest (S.map e.toEmbedding) (fun u => w (e.symm u))) =
    sampledSingleTestSeminorm F (normalizedSliceTest S w) := by
  ext v
  change ‖𝔼 u : T', v (F (e.symm u)) *
    normalizedSliceTest (S.map e.toEmbedding) (fun t => w (e.symm t)) u‖ =
      ‖𝔼 t : T, v (F t) * normalizedSliceTest S w t‖
  congr 1
  symm
  apply Fintype.expect_equiv e
  intro t
  rw [e.symm_apply_apply, normalizedSliceTest_equiv]

theorem sampledSliceSeminorm_coordinateEquiv
    {Ω Ω' T T' X : Type*} [Fintype Ω] [Fintype Ω'] [Fintype T] [Fintype T']
    (e : Ω ≃ Ω') (d : T ≃ T')
    (p : FiniteProbabilityWeights Ω) (p' : FiniteProbabilityWeights Ω')
    (hweight : ∀ z, p'.weight (e z) = p.weight z)
    {Tests : Ω → Type*} (F : Ω → T → X)
    (S : ∀ z, Tests z → Finset T) (w : ∀ z, Tests z → T → ℂ) :
    sampledSliceSeminorm p' (fun z t => F (e.symm z) (d.symm t))
      (fun z (j : Tests (e.symm z)) => (S (e.symm z) j).map d.toEmbedding)
      (fun z j t => w (e.symm z) j (d.symm t)) =
    sampledSliceSeminorm p F S w := by
  ext v
  change p'.mean (fun z =>
    (⨆ j : Tests (e.symm z), sampledSingleTestSeminorm
      (fun t => F (e.symm z) (d.symm t))
      (normalizedSliceTest ((S (e.symm z) j).map d.toEmbedding)
        (fun t => w (e.symm z) j (d.symm t)))) v) =
    p.mean (fun z => (⨆ j : Tests z, sampledSingleTestSeminorm (F z)
      (normalizedSliceTest (S z j) (w z j))) v)
  simp_rw [sampledSingleSliceSeminorm_equiv]
  unfold FiniteProbabilityWeights.mean
  symm
  apply Fintype.sum_equiv e
  intro z
  rw [hweight]
  exact congrArg (fun z' => p.weight z *
    (⨆ j : Tests z', sampledSingleTestSeminorm (F z')
      (normalizedSliceTest (S z' j) (w z' j))) v) (e.symm_apply_apply z).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {K K' X : Type*}

def scalarNoiseIndexEquiv (e : K ≃ K') : Option K × X ≃ Option K' × X :=
  (Equiv.optionCongr e).prodCongr (Equiv.refl X)

@[simp] theorem scalarNoiseIndexEquiv_none (e : K ≃ K') (x : X) :
    scalarNoiseIndexEquiv e (none, x) = (none, x) := rfl

@[simp] theorem scalarNoiseIndexEquiv_some (e : K ≃ K') (k : K) (x : X) :
    scalarNoiseIndexEquiv e (some k, x) = (some (e k), x) := rfl

@[simp] theorem scalarNoiseIndexEquiv_symm (e : K ≃ K') :
    (scalarNoiseIndexEquiv (X := X) e).symm = scalarNoiseIndexEquiv e.symm := rfl

@[simp] theorem trimmedSpatialWidths_scalarNoiseIndexEquiv
    (e : K ≃ K') (B τ : ℝ) (N : X → ℕ) (i : Option K × X) :
    trimmedSpatialWidths B τ N (scalarNoiseIndexEquiv e i) =
      trimmedSpatialWidths B τ N i := by
  rcases i with ⟨k, x⟩
  cases k <;> rfl

variable [Fintype K] [Fintype K'] [Fintype X]

noncomputable def scalarNoiseSupportEquiv (e : K ≃ K') (B τ : ℝ) (N : X → ℕ) :
    rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1 ≃
      rectangularWeightIndices 0 (trimmedSpatialWidths (K := K') B τ N) 1 where
  toFun z := ⟨fun j => z.val ((scalarNoiseIndexEquiv e).symm j), by
    apply (mem_rectangularWeightIndices_zero_iff _ _).mpr
    intro j
    simpa only [scalarNoiseIndexEquiv_symm,
      trimmedSpatialWidths_scalarNoiseIndexEquiv] using
      (mem_rectangularWeightIndices_zero_iff _ _).mp z.property
        ((scalarNoiseIndexEquiv e).symm j)⟩
  invFun z := ⟨fun i => z.val (scalarNoiseIndexEquiv e i), by
    apply (mem_rectangularWeightIndices_zero_iff _ _).mpr
    intro i
    simpa only [trimmedSpatialWidths_scalarNoiseIndexEquiv] using
      (mem_rectangularWeightIndices_zero_iff _ _).mp z.property
        (scalarNoiseIndexEquiv e i)⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    exact congrArg z.val ((scalarNoiseIndexEquiv e).symm_apply_apply i)
  right_inv z := by
    apply Subtype.ext
    funext j
    exact congrArg z.val ((scalarNoiseIndexEquiv e).apply_symm_apply j)

@[simp] theorem scalarNoiseSupportEquiv_val (e : K ≃ K') (B τ : ℝ)
    (N : X → ℕ)
    (z : rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    (scalarNoiseSupportEquiv e B τ N z).val =
      fun j => z.val ((scalarNoiseIndexEquiv e).symm j) := rfl

@[simp] theorem scalarNoiseSupportEquiv_symm_val (e : K ≃ K') (B τ : ℝ)
    (N : X → ℕ)
    (z : rectangularWeightIndices 0 (trimmedSpatialWidths (K := K') B τ N) 1) :
    ((scalarNoiseSupportEquiv e B τ N).symm z).val =
      fun i => z.val (scalarNoiseIndexEquiv e i) := rfl

noncomputable def scalarJointPathEquiv (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)
    (A : Type*) :
    A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1 ≃
      A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K') B τ N) 1 :=
  (Equiv.refl A).prodCongr (scalarNoiseSupportEquiv e B τ N)

@[simp] theorem scalarJointPathEquiv_fst (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)
    (A : Type*)
    (z : A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    (scalarJointPathEquiv e B τ N A z).1 = z.1 := rfl

@[simp] theorem scalarJointPathEquiv_snd_val (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)
    (A : Type*)
    (z : A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    (scalarJointPathEquiv e B τ N A z).2.val =
      fun j => z.2.val ((scalarNoiseIndexEquiv e).symm j) := rfl

namespace BooleanCubeKernel

omit [Fintype X] in

theorem jointIntegerPhysicalSite_scalarNoiseIndexEquiv (e : K ≃ K')
    (root : K → ℤ) (a : X → ℤ) (z : Option K × X → ℤ) :
    jointIntegerPhysicalSite (fun k' => root (e.symm k'))
        (a, fun j => z ((scalarNoiseIndexEquiv e).symm j)) =
      jointIntegerPhysicalSite root (a, z) := by
  funext x
  simp only [jointIntegerPhysicalSite, Pi.add_apply, integerPhysicalSite,
    scalarNoiseIndexEquiv_symm, scalarNoiseIndexEquiv_none, scalarNoiseIndexEquiv_some]
  congr 2
  exact e.symm.sum_comp (fun k => root k * z (some k, x))

theorem jointIntegerPhysicalSite_scalarNoiseSupportEquiv (e : K ≃ K')
    (B τ : ℝ) (N : X → ℕ) (root : K → ℤ) (a : X → ℤ)
    (z : rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    jointIntegerPhysicalSite (fun k' => root (e.symm k'))
        (a, (scalarNoiseSupportEquiv e B τ N z).val) =
      jointIntegerPhysicalSite root (a, z.val) :=
  jointIntegerPhysicalSite_scalarNoiseIndexEquiv e root a z.val

theorem jointIntegerPhysicalSite_scalarJointPathEquiv (e : K ≃ K')
    (B τ : ℝ) (N : X → ℕ) (A : Finset (X → ℤ)) (root : K → ℤ)
    (z : A × rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1) :
    jointIntegerPhysicalSite (fun k' => root (e.symm k'))
        ((scalarJointPathEquiv e B τ N A z).1.val,
          (scalarJointPathEquiv e B τ N A z).2.val) =
      jointIntegerPhysicalSite root (z.1.val, z.2.val) :=
  jointIntegerPhysicalSite_scalarNoiseIndexEquiv e root z.1.val z.2.val

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K K' X : Type*} [Fintype K] [Fintype K'] [Fintype X]
    (e : K ≃ K') (B τ : ℝ) (N : X → ℕ)

local notation "W" => trimmedSpatialWidths (K := K) B τ N
local notation "W'" => trimmedSpatialWidths (K := K') B τ N

include e in
theorem selectedResidueSmoothMass_scalarCoordinateEquiv :
    (∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W' z) =
      ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z :=
  selectedResidueSmoothMass_one_reindex (scalarNoiseIndexEquiv e) W W'
    (trimmedSpatialWidths_scalarNoiseIndexEquiv e B τ N)

variable (hW : ∀ i : Option K × X, 0 < trimmedSpatialWidths B τ N i)
    (hW' : ∀ i : Option K' × X, 0 < trimmedSpatialWidths B τ N i)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) B τ N) z)
    (hZ' : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K') B τ N) z)

include hW hW' hZ hZ'

theorem selectedResidueFiniteLaw_scalarCoordinateEquiv_weight
    (z : rectangularWeightIndices 0 W 1) :
    (selectedResidueFiniteLaw (fun _ : X => 1) {0} W' hW' hZ').weight
        (scalarNoiseSupportEquiv e B τ N z) =
      (selectedResidueFiniteLaw (fun _ : X => 1) {0} W hW hZ).weight z := by
  change selectedResidueSmoothWeight (fun _ : X => 1) {0} W'
      (scalarNoiseSupportEquiv e B τ N z).val /
      (∑' y, selectedResidueSmoothWeight (fun _ : X => 1) {0} W' y) =
    selectedResidueSmoothWeight (fun _ : X => 1) {0} W z.val /
      (∑' y, selectedResidueSmoothWeight (fun _ : X => 1) {0} W y)
  exact congrArg₂ (fun a b : ℝ => a / b)
    (selectedResidueSmoothWeight_one_reindex (scalarNoiseIndexEquiv e) W W'
      (trimmedSpatialWidths_scalarNoiseIndexEquiv e B τ N) z.val)
    (selectedResidueSmoothMass_scalarCoordinateEquiv e B τ N)

variable {Y : Type*} (A : Finset Y) (hA : A.Nonempty)

theorem selectedJointReference_scalarCoordinateEquiv_weight
    (z : A × rectangularWeightIndices 0 W 1) :
    (selectedJointReference A hA (fun _ : X => 1) {0} W' hW' hZ').weight
        (scalarJointPathEquiv e B τ N A z) =
      (selectedJointReference A hA (fun _ : X => 1) {0} W hW hZ).weight z := by
  change (FiniteProbabilityWeights.uniformFinset A hA).weight z.1 *
      (selectedResidueFiniteLaw (fun _ : X => 1) {0} W' hW' hZ').weight
        (scalarNoiseSupportEquiv e B τ N z.2) =
    (FiniteProbabilityWeights.uniformFinset A hA).weight z.1 *
      (selectedResidueFiniteLaw (fun _ : X => 1) {0} W hW hZ).weight z.2
  rw [selectedResidueFiniteLaw_scalarCoordinateEquiv_weight e B τ N hW hW' hZ hZ']

theorem selectedJointReference_scalarCoordinateEquiv_mean
    (f : A × rectangularWeightIndices 0 W' 1 → ℝ) :
    (selectedJointReference A hA (fun _ : X => 1) {0} W hW hZ).mean
        (fun z => f (scalarJointPathEquiv e B τ N A z)) =
      (selectedJointReference A hA (fun _ : X => 1) {0} W' hW' hZ').mean f := by
  unfold FiniteProbabilityWeights.mean
  apply Fintype.sum_equiv (scalarJointPathEquiv e B τ N A)
  intro z
  rw [selectedJointReference_scalarCoordinateEquiv_weight e B τ N hW hW' hZ hZ' A hA]

theorem selectedJointReference_scalarCoordinateEquiv_complexMean
    (f : A × rectangularWeightIndices 0 W' 1 → ℂ) :
    (selectedJointReference A hA (fun _ : X => 1) {0} W hW hZ).complexMean
        (fun z => f (scalarJointPathEquiv e B τ N A z)) =
      (selectedJointReference A hA (fun _ : X => 1) {0} W' hW' hZ').complexMean f := by
  unfold FiniteProbabilityWeights.complexMean
  apply Fintype.sum_equiv (scalarJointPathEquiv e B τ N A)
  intro z
  rw [selectedJointReference_scalarCoordinateEquiv_weight e B τ N hW hW' hZ hZ' A hA]

theorem selectedJointReference_scalarCoordinateEquiv_mass
    (retained : Finset (A × rectangularWeightIndices 0 W 1)) :
    (selectedJointReference A hA (fun _ : X => 1) {0} W' hW' hZ').mass
        (retained.image (scalarJointPathEquiv e B τ N A)) =
      (selectedJointReference A hA (fun _ : X => 1) {0} W hW hZ).mass retained := by
  classical
  unfold FiniteProbabilityWeights.mass
  rw [Finset.sum_image (scalarJointPathEquiv e B τ N A).injective.injOn]
  apply Finset.sum_congr rfl
  intro z _
  exact selectedJointReference_scalarCoordinateEquiv_weight e B τ N hW hW' hZ hZ' A hA z

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def OrdinarySliceNativeDetection
    {m degree : ℕ} {X K Ω : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] [Fintype Ω]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sides : K → ℕ) (law : FiniteProbabilityWeights Ω)
    (physical : Ω → integerBox sides → X → ℤ) (pSlice pTest pNative α : ℝ) : Prop :=
  ∀ {Tests : Ω → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : K => 1))
    (slices : ∀ z, Tests z → Finset (integerBox sides))
    (origin : ∀ z, Tests z → K → ℤ) (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → K → ℕ),
    (∀ z j, 0 < step z j) →
    (∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j)) →
    (∀ z j, IsDenseCommonStrideBox sides pSlice ((slices z j).image Subtype.val)) →
    (∀ z j, (Vdetect z j).ComplexityLE pTest) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    SampledSliceNativeDetection J N hbox poly law physical slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val)))
      degree pNative α

private theorem niltestSliceSeminorm_coordinateEquiv
    {degree : ℕ} {X K K' Ω Ω' : Type}
    [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    [Fintype Ω] [Fintype Ω']
    (e : K ≃ K') (ep : Ω ≃ Ω') (sides : K → ℕ)
    (law : FiniteProbabilityWeights Ω) (law' : FiniteProbabilityWeights Ω')
    (hweight : ∀ z, law'.weight (ep z) = law.weight z)
    (physical : Ω → integerBox sides → X)
    {Tests : Ω → Type}
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : K => 1))
    (slices : ∀ z, Tests z → Finset (integerBox sides))
    (origin : ∀ z, Tests z → K → ℤ) (step : ∀ z, Tests z → ℕ) :
    sampledSliceSeminorm law'
      (fun z t => physical (ep.symm z) ((integerBoxCoordinateEquiv e sides).symm t))
      (fun z (j : Tests (ep.symm z)) =>
        (slices (ep.symm z) j).map (integerBoxCoordinateEquiv e sides).toEmbedding)
      (fun z j t => star (((V (ep.symm z) j).coordinateEquiv e).eval
        (commonStrideIndex (integerPointCoordinateEquiv e (origin (ep.symm z) j))
          (step (ep.symm z) j) t.val))) =
    sampledSliceSeminorm law physical slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (origin z j) (step z j) t.val))) := by
  have hcoord (z : Ω') (j : Tests (ep.symm z))
      (t : integerBox (coordinateReindexedSides e sides)) :
      ((V (ep.symm z) j).coordinateEquiv e).eval
        (commonStrideIndex (integerPointCoordinateEquiv e (origin (ep.symm z) j))
          (step (ep.symm z) j) t.val) =
      (V (ep.symm z) j).eval
        (commonStrideIndex (origin (ep.symm z) j) (step (ep.symm z) j)
          ((integerBoxCoordinateEquiv e sides).symm t).val) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_coordinateEquiv]
    congr 1
    funext k
    simp only [commonStrideIndex, integerPointCoordinateEquiv_apply,
      Equiv.symm_apply_apply, integerBoxCoordinateEquiv_symm_val,
      integerPointCoordinateEquiv_symm_apply]
  simp_rw [hcoord]
  exact sampledSliceSeminorm_coordinateEquiv ep (integerBoxCoordinateEquiv e sides)
    law law' hweight physical slices
    (fun z j t => star ((V z j).eval (commonStrideIndex (origin z j) (step z j) t.val)))

theorem OrdinarySliceNativeDetection.coordinateReturn
    {m degree : ℕ} {X K K' Ω Ω' : Type}
    [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
    [Fintype K'] [DecidableEq K'] [Fintype Ω] [Fintype Ω']
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (e : K ≃ K') (ep : Ω ≃ Ω') (sides : K → ℕ)
    (law : FiniteProbabilityWeights Ω) (law' : FiniteProbabilityWeights Ω')
    (hweight : ∀ z, law'.weight (ep z) = law.weight z)
    (physical : Ω → integerBox sides → X → ℤ)
    (physical' : Ω' → integerBox (coordinateReindexedSides e sides) → X → ℤ)
    (hphysical : ∀ z t, physical' (ep z) (integerBoxCoordinateEquiv e sides t) = physical z t)
    (pSlice pTest pNative α : ℝ)
    (h : OrdinarySliceNativeDetection (degree := degree) J N hbox poly
      (coordinateReindexedSides e sides) law' physical' pSlice pTest pNative α) :
    OrdinarySliceNativeDetection (degree := degree) J N hbox poly
      sides law physical pSlice pTest pNative α := by
  have hphys : physical' = fun z t =>
      physical (ep.symm z) ((integerBoxCoordinateEquiv e sides).symm t) := by
    funext z t
    simpa only [Equiv.apply_symm_apply] using
      hphysical (ep.symm z) ((integerBoxCoordinateEquiv e sides).symm t)
  subst physical'
  intro Tests _ Ldetect _ _ dims _ _ _ _ D V slices origin step length
    hstep hshape hdense hcomplex hnorm
  let es := integerBoxCoordinateEquiv e sides
  let slices' := fun z (j : Tests (ep.symm z)) => (slices (ep.symm z) j).map es.toEmbedding
  have himage (z : Ω') (j : Tests (ep.symm z)) :
      (slices' z j).image Subtype.val =
        ((slices (ep.symm z) j).image Subtype.val).image (integerPointCoordinateEquiv e) := by
    simp only [slices', Finset.map_eq_image, Equiv.coe_toEmbedding, Finset.image_image]
    rfl
  have hshape' (z : Ω') (j : Tests (ep.symm z)) :
      (slices' z j).image Subtype.val =
        commonStrideBox (integerPointCoordinateEquiv e (origin (ep.symm z) j))
          (step (ep.symm z) j) (coordinateReindexedSides e (length (ep.symm z) j)) := by
    rw [himage, hshape, commonStrideBox_image_coordinateEquiv]
  have hdense' (z : Ω') (j : Tests (ep.symm z)) :
      IsDenseCommonStrideBox (coordinateReindexedSides e sides) pSlice
        ((slices' z j).image Subtype.val) := by
    rw [himage]
    exact (hdense (ep.symm z) j).coordinateEquiv e
  have hdet := h (fun z j => D (ep.symm z) j)
    (fun z j => (V (ep.symm z) j).coordinateEquiv e) slices'
    (fun z j => integerPointCoordinateEquiv e (origin (ep.symm z) j))
    (fun z j => step (ep.symm z) j)
    (fun z j => coordinateReindexedSides e (length (ep.symm z) j))
    (fun z j => hstep (ep.symm z) j) hshape' hdense'
    (fun z j => hcomplex (ep.symm z) j) (fun z j => hnorm (ep.symm z) j)
  have hseminorm := niltestSliceSeminorm_coordinateEquiv e ep sides law law' hweight
    physical D V slices origin step

  intro signal hsignal hsupp hlarge
  exact hdet signal hsignal hsupp (by rw [hseminorm]; exact hlarge)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

def ScalarReferenceNativeDetection
    {m degree : ℕ} {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (S : ℕ) (W τ : ℝ)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hW : ∀ z : Option K × X, 0 < trimmedSpatialWidths W τ N z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) W τ N) z)
    (pSlice pTest pNative α : ℝ) : Prop :=
  OrdinarySliceNativeDetection (degree := degree) J N hbox poly (fun _ : K => S)
    (selectedJointReference _ hbase (fun _ : X => 1) {0}
      (trimmedSpatialWidths W τ N) hW hZ)
    (fun z t => jointIntegerPhysicalSite t.val (z.1.val, z.2.val))
    pSlice pTest pNative α

theorem ScalarReferenceNativeDetection.coordinateReturn
    {m degree : ℕ} {X K K' : Type}
    [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
    [Fintype K'] [DecidableEq K']
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (e : K ≃ K') (S : ℕ) (W τ : ℝ)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hW : ∀ z : Option K × X, 0 < trimmedSpatialWidths W τ N z)
    (hW' : ∀ z : Option K' × X, 0 < trimmedSpatialWidths W τ N z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) W τ N) z)
    (hZ' : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K') W τ N) z)
    (pSlice pTest pNative α : ℝ)
    (h : ScalarReferenceNativeDetection (degree := degree) J N hbox poly S W τ
      hbase hW' hZ' pSlice pTest pNative α) :
    ScalarReferenceNativeDetection (degree := degree) J N hbox poly S W τ
      hbase hW hZ pSlice pTest pNative α := by
  exact OrdinarySliceNativeDetection.coordinateReturn J N hbox poly e
    (scalarJointPathEquiv e W τ N _) (fun _ : K => S)
    (selectedJointReference _ hbase _ _ _ hW hZ)
    (selectedJointReference _ hbase _ _ _ hW' hZ')
    (selectedJointReference_scalarCoordinateEquiv_weight e W τ N hW hW' hZ hZ' _ hbase)
    (fun z t => jointIntegerPhysicalSite t.val (z.1.val, z.2.val))
    (fun z t => jointIntegerPhysicalSite t.val (z.1.val, z.2.val))
    (fun z t => jointIntegerPhysicalSite_scalarJointPathEquiv e W τ N _ t.val z)
    pSlice pTest pNative α h

theorem ScalarReferenceNativeDetection.retag_of_isEmpty
    {m m' degree : ℕ} {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K]
    (J : Fin m → Type) [∀ j, Fintype (J j)] [IsEmpty (Σ j, J j)]
    (J' : Fin m' → Type) [∀ j, Fintype (J' j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (poly' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ))
    (S : ℕ) (W τ : ℝ)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hW : ∀ z : Option K × X, 0 < trimmedSpatialWidths W τ N z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := K) W τ N) z)
    (pSlice pTest pNative α : ℝ)
    (h : ScalarReferenceNativeDetection (degree := degree) J N hbox poly S W τ
      hbase hW hZ pSlice pTest pNative α) :
    ScalarReferenceNativeDetection (degree := degree) J' N hbox poly' S W τ
      hbase hW hZ pSlice pTest pNative α := by
  intro Tests _ Ldetect _ _ dims _ _ _ _ D V slices origin step length
    hstep hshape hdense hcomplex hnorm
  exact (h D V slices origin step length hstep hshape hdense hcomplex hnorm).retag_of_isEmpty
    J J' N hbox poly poly' _ _ _ _ degree pNative α

end Erdos3.VectorPolynomial

end

end OAI
