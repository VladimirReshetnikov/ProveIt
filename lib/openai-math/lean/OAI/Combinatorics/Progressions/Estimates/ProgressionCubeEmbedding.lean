import OAI.Combinatorics.Progressions.Estimates.SmoothCoefficientSlice
import OAI.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
import OAI.Combinatorics.Progressions.Probability.TranslatedWeightedCubeLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem shiftScalarCubeResidues_neg_cancel {I : Type*} (c : ℤ) (m : Option I → ℕ)
    (r : ∀ i, ZMod (m i)) :
    shiftScalarCubeResidues c m (shiftScalarCubeResidues (-c) m r) = r := by
  funext i
  cases i <;> simp [shiftScalarCubeResidues]

namespace NormalizedScalarCubeSource

abbrev SliceDomain {q : ℕ} (s : NormalizedScalarCubeSource (Fin q)) (c : ℤ) :=
  TranslatedResidueSupportedCube q s.length c s.modulus (shiftScalarCubeResidues (-c) s.modulus s.residue)

theorem baseLaw_slice_mean {q : ℕ} (s : NormalizedScalarCubeSource (Fin q)) (c : ℤ)
    (f : (Option (Fin q) → ℤ) → ℝ) :
    s.baseLaw.mean (fun x => f (shiftScalarCube c (fun i => (x i : ℤ)))) =
      𝔼 p : s.SliceDomain c, f (supportedCubeCoordinates p.val.val) := by
  have he := scalarCubeResidueWeights_translated_mean q s.length s.modulusBound c s.length_pos s.modulus
    (shiftScalarCubeResidues (-c) s.modulus s.residue) s.modulus_pos s.modulus_le s.size f
  simpa only [shiftScalarCubeResidues_neg_cancel, baseLaw] using he

noncomputable def sliceDensity {q : ℕ} (s : NormalizedScalarCubeSource (Fin q)) (c : ℤ)
    (p : s.SliceDomain c) : ℝ :=
  translatedCubeWeight s.length c s.weight (supportedCubeCoordinates p.val.val)

theorem sliceDensity_nonneg {q : ℕ} (s : NormalizedScalarCubeSource (Fin q)) (c : ℤ)
    (p : s.SliceDomain c) : 0 ≤ s.sliceDensity c p := (s.weight_range _).1

theorem sliceDensity_mean_one {q : ℕ} (s : NormalizedScalarCubeSource (Fin q)) (c : ℤ) :
    (𝔼 p : s.SliceDomain c, s.sliceDensity c p) = 1 := by
  have he := s.baseLaw_slice_mean c (translatedCubeWeight s.length c s.weight)
  simpa only [translatedCubeWeight, shiftScalarCube_neg_shift, baseLaw, s.normalized, sliceDensity] using he.symm

noncomputable def sliceWeights {q : ℕ} (s : NormalizedScalarCubeSource (Fin q)) (c : ℤ) :
    FiniteProbabilityWeights (s.SliceDomain c) :=
  FiniteProbabilityWeights.ofDensity (s.sliceDensity c) (s.sliceDensity_nonneg c) (s.sliceDensity_mean_one c)

theorem source_slice_mean {q : ℕ} (s : NormalizedScalarCubeSource (Fin q)) (c : ℤ)
    (f : (Option (Fin q) → ℤ) → ℝ) :
    s.source.mean (fun x => f (shiftScalarCube c (fun i => (x i : ℤ)))) =
      (s.sliceWeights c).mean (fun p => f (supportedCubeCoordinates p.val.val)) := by
  apply (FiniteProbabilityWeights.reweight_mean s.baseLaw
    (fun z => s.weight (fun i => (z i : ℝ) / s.length))
    (fun z => (s.weight_range (fun i => (z i : ℝ) / s.length)).1) s.normalized
    (fun x => f (shiftScalarCube c (fun i => (x i : ℤ))))).trans
  rw [sliceWeights, FiniteProbabilityWeights.ofDensity_mean]
  have he := s.baseLaw_slice_mean c (fun y => translatedCubeWeight s.length c s.weight y * f y)
  simpa only [sliceDensity, translatedCubeWeight, shiftScalarCube_neg_shift] using he

theorem source_slice_complexMean {q : ℕ} (s : NormalizedScalarCubeSource (Fin q)) (c : ℤ)
    (f : (Option (Fin q) → ℤ) → ℂ) :
    s.source.complexMean (fun x => f (shiftScalarCube c (fun i => (x i : ℤ)))) =
      (s.sliceWeights c).complexMean (fun p => f (supportedCubeCoordinates p.val.val)) := by
  apply Complex.ext
  · rw [FiniteProbabilityWeights.complexMean_re, FiniteProbabilityWeights.complexMean_re]
    exact s.source_slice_mean c (fun x => (f x).re)
  · rw [FiniteProbabilityWeights.complexMean_im, FiniteProbabilityWeights.complexMean_im]
    exact s.source_slice_mean c (fun x => (f x).im)

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

structure FiniteCubeSlice (q : ℕ) where
  length : ℕ
  root : ℤ
  modulus : Option (Fin q) → ℕ
  residue : ∀ i, ZMod (modulus i)

namespace FiniteCubeSlice

abbrev Domain {q : ℕ} (s : FiniteCubeSlice q) :=
  TranslatedResidueSupportedCube q s.length s.root s.modulus s.residue

def coordinates {q : ℕ} (s : FiniteCubeSlice q) (x : s.Domain) : Option (Fin q) → ℤ :=
  supportedCubeCoordinates x.val.val

def radius {q : ℕ} (s : FiniteCubeSlice q) : ℕ := s.root.natAbs + s.length

theorem coordinates_abs_le {q : ℕ} (s : FiniteCubeSlice q) (x : s.Domain) (i : Option (Fin q)) :
    |s.coordinates x i| ≤ (s.radius : ℤ) := by
  have hb : s.root ≤ x.val.val.2 ∧ x.val.val.2 < s.root + s.length := x.val.base_mem
  rw [radius, Nat.cast_add, Int.natCast_natAbs]
  cases i with
  | none =>
      change |x.val.val.2| ≤ _
      have hd : |x.val.val.2 - s.root| ≤ (s.length : ℤ) := by
        rw [abs_le]
        constructor <;> omega
      calc
        _ = |s.root + (x.val.val.2 - s.root)| := by congr 1; ring
        _ ≤ |s.root| + |x.val.val.2 - s.root| := abs_add_le _ _
        _ ≤ _ := add_le_add le_rfl hd
  | some i =>
      have ha : s.root ≤ x.val.val.2 + x.val.val.1 i ∧
          x.val.val.2 + x.val.val.1 i < s.root + s.length := x.val.axis_mem i
      change |x.val.val.1 i| ≤ _
      have hd : |x.val.val.1 i| ≤ (s.length : ℤ) := by
        rw [abs_le]
        constructor <;> omega
      exact hd.trans (le_add_of_nonneg_left (abs_nonneg _))

theorem radius_relative {q : ℕ} (s : FiniteCubeSlice q) {O : ℝ}
    (hroot : |(s.root : ℝ)| ≤ O * s.length) :
    (s.radius : ℝ) ≤ (O + 1) * s.length := by
  simp only [radius, Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]
  nlinarith

end FiniteCubeSlice

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def cubeSliceEmbedding {q : ℕ} (s : FiniteCubeSlice q) (P : Set ℤ)
    (hP : Set.Ico s.root (s.root + s.length) ⊆ P) : s.Domain ↪ SupportedCube q P where
  toFun x := ⟨x.val.val, fun ω => hP (x.val.property ω)⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : SupportedCube q P => z.val) h

theorem cubeSliceEmbedding_coordinates {q : ℕ} (s : FiniteCubeSlice q) (P : Set ℤ)
    (hP : Set.Ico s.root (s.root + s.length) ⊆ P) (x : s.Domain) :
    supportedCubeCoordinates (cubeSliceEmbedding s P hP x).val = s.coordinates x := rfl

noncomputable def cubeSliceEvent {q : ℕ} (s : FiniteCubeSlice q) (P : Set ℤ) [Finite P] :
    Finset (SupportedCube q P) :=
  Finset.univ.filter (fun x =>
    (∀ ω : Fin q → Bool, x.val.2 + cubeShift x.val.1 ω ∈ Set.Ico s.root (s.root + s.length)) ∧
    ∀ i, ((supportedCubeCoordinates x.val i : ℤ) : ZMod (s.modulus i)) = s.residue i)

theorem cubeSliceEmbedding_range {q : ℕ} (s : FiniteCubeSlice q) (P : Set ℤ) [Finite P]
    (hP : Set.Ico s.root (s.root + s.length) ⊆ P) :
    finiteEmbeddingRange (cubeSliceEmbedding s P hP) = cubeSliceEvent s P := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
    subst x
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.val.property, y.property⟩
  · intro hx
    obtain ⟨hvertices, hres⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_map.mpr ⟨⟨⟨x.val, hvertices⟩, hres⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    rfl

noncomputable def conditionCubeSlice {q : ℕ} (s : FiniteCubeSlice q) (P : Set ℤ) [Finite P]
    (hP : Set.Ico s.root (s.root + s.length) ⊆ P)
    (w : (Option (Fin q) → ℤ) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hmass : 0 < ∑ x : s.Domain, w (s.coordinates x)) : FiniteProbabilityWeights (SupportedCube q P) :=
  FiniteProbabilityWeights.conditionAlongEmbedding (fun x => w (supportedCubeCoordinates x.val))
    (fun x => hw (supportedCubeCoordinates x.val)) (cubeSliceEmbedding s P hP) hmass

theorem conditionCubeSlice_complexMean {q : ℕ} (s : FiniteCubeSlice q) (P : Set ℤ) [Finite P]
    (hP : Set.Ico s.root (s.root + s.length) ⊆ P)
    (w : (Option (Fin q) → ℤ) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hmass : 0 < ∑ x : s.Domain, w (s.coordinates x)) (f : (Option (Fin q) → ℤ) → ℂ) :
    (conditionCubeSlice s P hP w hw hmass).complexMean (fun x => f (supportedCubeCoordinates x.val)) =
      (FiniteProbabilityWeights.ofPositiveWeights (fun x : s.Domain => w (s.coordinates x))
        (fun x => hw (s.coordinates x)) hmass).complexMean (fun x => f (s.coordinates x)) :=
  FiniteProbabilityWeights.conditionAlongEmbedding_complexMean _ _ (cubeSliceEmbedding s P hP)
    hmass (fun x => f (supportedCubeCoordinates x.val))

theorem uniform_condition_cubeSlice_mean {q : ℕ} (s : FiniteCubeSlice q) (P : Set ℤ) [Finite P]
    [Nonempty (SupportedCube q P)] (hP : Set.Ico s.root (s.root + s.length) ⊆ P)
    (hmass : 0 < (FiniteProbabilityWeights.uniform (SupportedCube q P)).mass
      (finiteEmbeddingRange (cubeSliceEmbedding s P hP))) (f : (Option (Fin q) → ℤ) → ℝ) :
    ((FiniteProbabilityWeights.uniform (SupportedCube q P)).condition
      (finiteEmbeddingRange (cubeSliceEmbedding s P hP)) hmass).mean
        (fun x => f (supportedCubeCoordinates x.val)) = 𝔼 x : s.Domain, f (s.coordinates x) := by
  refine (FiniteProbabilityWeights.uniform_condition_embedding_mean (cubeSliceEmbedding s P hP)
    hmass (fun x : SupportedCube q P => f (supportedCubeCoordinates x.val))).trans ?_
  apply Finset.expect_congr
  · apply Finset.ext
    intro x
    exact ⟨fun _ => Finset.mem_univ x, fun _ => Finset.mem_univ x⟩
  · intro x _
    rfl

end Erdos3

end

section

namespace Erdos3

namespace FiniteCubeSlice

def domainEquiv {q : ℕ} {s t : FiniteCubeSlice q} (h : s = t) : s.Domain ≃ t.Domain :=
  Equiv.cast (congrArg (fun u : FiniteCubeSlice q => u.Domain) h)

theorem coordinates_domainEquiv {q : ℕ} {s t : FiniteCubeSlice q} (h : s = t) (x : s.Domain) :
    t.coordinates (domainEquiv h x) = s.coordinates x := by
  cases h
  rfl

end FiniteCubeSlice

namespace FiniteCoefficientSlice

def domainEquiv {s t : FiniteCoefficientSlice} (h : s = t) : s.Domain ≃ t.Domain :=
  Equiv.cast (congrArg (fun u : FiniteCoefficientSlice => u.Domain) h)

theorem value_domainEquiv {s t : FiniteCoefficientSlice} (h : s = t) (x : s.Domain) :
    t.value (domainEquiv h x) = s.value x := by
  cases h
  rfl

theorem index_domainEquiv {s t : FiniteCoefficientSlice} (h : s = t) (x : s.Domain) :
    (domainEquiv h x).val = x.val := by
  cases h
  rfl

end FiniteCoefficientSlice

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

structure RetainedCubeSlice (q M : ℕ) (B T η : ℝ≥0) where
  length : ℕ
  root : ℤ
  modulus : Option (Fin q) → ℕ
  residue : ∀ i, ZMod (modulus i)
  modulus_pos : ∀ i, 0 < modulus i
  modulus_le : ∀ i, modulus i ≤ M
  weight : (Option (Fin q) → ℝ) → ℝ
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ B
  weight_lipschitz : LipschitzWith T weight
  mean_lower : (η : ℝ) ≤
    𝔼 x : TranslatedResidueSupportedCube q length root modulus (shiftScalarCubeResidues (-root) modulus residue),
      translatedCubeWeight length root weight (supportedCubeCoordinates x.val.val)

namespace RetainedCubeSlice

variable {q M : ℕ} {B T η : ℝ≥0} (s : RetainedCubeSlice q M B T η)

def finiteSlice : FiniteCubeSlice q where
  length := s.length
  root := s.root
  modulus := s.modulus
  residue := shiftScalarCubeResidues (-s.root) s.modulus s.residue

abbrev Domain := s.finiteSlice.Domain

noncomputable def sliceWeight (x : s.Domain) : ℝ :=
  translatedCubeWeight s.length s.root s.weight (s.finiteSlice.coordinates x)

theorem sliceWeight_nonneg (x : s.Domain) : 0 ≤ s.sliceWeight x := (s.weight_range _).1

theorem total_pos (hη : 0 < η) : 0 < ∑ x, s.sliceWeight x :=
  FiniteProbabilityWeights.sum_pos_of_expect_pos _ ((show (0 : ℝ) < η from hη).trans_le s.mean_lower)

noncomputable def law (hη : 0 < η) : FiniteProbabilityWeights s.Domain :=
  FiniteProbabilityWeights.ofPositiveWeights s.sliceWeight s.sliceWeight_nonneg (s.total_pos hη)

theorem length_pos_of_size (hsize : (q + 1) * M ≤ s.length) : 0 < s.length := by
  have hM : 0 < M := (s.modulus_pos none).trans_le (s.modulus_le none)
  exact (Nat.mul_pos (by omega : 0 < q + 1) hM).trans_le hsize

noncomputable def normalizer (hsize : (q + 1) * M ≤ s.length) : ℝ :=
  (scalarCubeResidueWeights (Fin q) s.length M (s.length_pos_of_size hsize) s.modulus s.residue
    s.modulus_pos s.modulus_le (by simpa only [Fintype.card_fin] using hsize)).mean
    (fun z => s.weight (fun i => (z i : ℝ) / s.length))

theorem normalizer_eq_mean (hsize : (q + 1) * M ≤ s.length) :
    s.normalizer hsize = 𝔼 x : s.Domain, s.sliceWeight x := by
  have he := scalarCubeResidueWeights_translated_mean q s.length M s.root (s.length_pos_of_size hsize)
    s.modulus (shiftScalarCubeResidues (-s.root) s.modulus s.residue)
    s.modulus_pos s.modulus_le (by simpa only [Fintype.card_fin] using hsize)
    (translatedCubeWeight s.length s.root s.weight)
  simp only [shiftScalarCubeResidues_neg_cancel, translatedCubeWeight, shiftScalarCube_neg_shift] at he
  apply he.trans
  apply Finset.expect_congr
  · apply congrArg (fun f : Fintype s.Domain => @Finset.univ _ f)
    exact Subsingleton.elim _ _
  · intro x _
    rfl

theorem normalizer_lower (hsize : (q + 1) * M ≤ s.length) : (η : ℝ) ≤ s.normalizer hsize := by
  rw [s.normalizer_eq_mean]
  exact s.mean_lower

noncomputable def normalized (hB : 0 < B) (hη : 0 < η) (hsize : (q + 1) * M ≤ s.length) :
    NormalizedScalarCubeSource (Fin q) :=
  normalizedScalarCubeSourceOfMeanLower (Fin q) s.length M (s.length_pos_of_size hsize)
    s.modulus s.residue s.modulus_pos s.modulus_le (by simpa only [Fintype.card_fin] using hsize)
    s.weight B T η hB hη s.weight_range s.weight_lipschitz (s.normalizer_lower hsize)

theorem normalized_sliceDensity (hB : 0 < B) (hη : 0 < η) (hsize : (q + 1) * M ≤ s.length)
    (x : s.Domain) :
    (s.normalized hB hη hsize).sliceDensity s.root x = s.sliceWeight x / s.normalizer hsize := rfl

theorem normalized_sliceWeights (hB : 0 < B) (hη : 0 < η) (hsize : (q + 1) * M ≤ s.length) :
    (s.normalized hB hη hsize).sliceWeights s.root = s.law hη := by
  have hZ : 0 < s.normalizer hsize := (show (0 : ℝ) < η from hη).trans_le (s.normalizer_lower hsize)
  exact FiniteProbabilityWeights.ofDensity_div_eq_ofPositiveWeights s.sliceWeight s.sliceWeight_nonneg
    (s.total_pos hη) hZ ((s.normalized hB hη hsize).sliceDensity_mean_one s.root)

end RetainedCubeSlice

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal Classical

structure SmoothCubeSlice (q M : ℕ) (B T : ℝ≥0) where
  length : ℕ
  root : ℤ
  modulus : Option (Fin q) → ℕ
  residue : ∀ i, ZMod (modulus i)
  modulus_pos : ∀ i, 0 < modulus i
  modulus_le : ∀ i, modulus i ≤ M
  weight : (Option (Fin q) → ℝ) → ℝ
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ B
  weight_lipschitz : LipschitzWith T weight
  weight_integral : ∫ x, weight x ∂scalarCubeMeasure (Fin q) = 1

namespace SmoothCubeSlice

variable {q M : ℕ} {B T : ℝ≥0} (s : SmoothCubeSlice q M B T)

def finiteSlice : FiniteCubeSlice q where
  length := s.length
  root := s.root
  modulus := s.modulus
  residue := shiftScalarCubeResidues (-s.root) s.modulus s.residue

abbrev Domain := s.finiteSlice.Domain

noncomputable def sliceWeight (x : s.Domain) : ℝ :=
  translatedCubeWeight s.length s.root s.weight (s.finiteSlice.coordinates x)

theorem sliceWeight_nonneg (x : s.Domain) : 0 ≤ s.sliceWeight x := (s.weight_range _).1

noncomputable def law (hmass : 0 < ∑ x, s.sliceWeight x) : FiniteProbabilityWeights s.Domain :=
  FiniteProbabilityWeights.ofPositiveWeights s.sliceWeight s.sliceWeight_nonneg hmass

noncomputable def longNormalizer (h : scalarCubeNormalizationThreshold (Fin q) M B T ≤ s.length) : ℝ :=
  (scalarCubeResidueWeights (Fin q) s.length M (scalarCubeNormalizationThreshold_spec (Fin q) h).1
    s.modulus s.residue s.modulus_pos s.modulus_le
    (scalarCubeNormalizationThreshold_spec (Fin q) h).2.1).mean
    (fun z => s.weight (fun i => (z i : ℝ) / s.length))

theorem longNormalizer_bounds (h : scalarCubeNormalizationThreshold (Fin q) M B T ≤ s.length) :
    1 / 2 ≤ s.longNormalizer h ∧ s.longNormalizer h ≤ 3 / 2 :=
  scalarCube_weight_normalizer_of_threshold (Fin q) s.length M s.modulus s.residue
    s.modulus_pos s.modulus_le s.weight s.weight_range s.weight_lipschitz s.weight_integral h

theorem longNormalizer_eq_expect (h : scalarCubeNormalizationThreshold (Fin q) M B T ≤ s.length) :
    s.longNormalizer h = 𝔼 x : s.Domain, s.sliceWeight x := by
  have he := scalarCubeResidueWeights_translated_mean q s.length M s.root
    (scalarCubeNormalizationThreshold_spec (Fin q) h).1 s.modulus
    (shiftScalarCubeResidues (-s.root) s.modulus s.residue) s.modulus_pos s.modulus_le
    (scalarCubeNormalizationThreshold_spec (Fin q) h).2.1
    (translatedCubeWeight s.length s.root s.weight)
  simp only [shiftScalarCubeResidues_neg_cancel, translatedCubeWeight, shiftScalarCube_neg_shift] at he
  apply he.trans
  apply Finset.expect_congr
  · apply Finset.ext
    intro x
    exact ⟨fun _ => Finset.mem_univ x, fun _ => Finset.mem_univ x⟩
  · intro x _
    rfl

theorem long_total_pos (h : scalarCubeNormalizationThreshold (Fin q) M B T ≤ s.length) :
    0 < ∑ x, s.sliceWeight x := by
  apply FiniteProbabilityWeights.sum_pos_of_expect_pos
  rw [← s.longNormalizer_eq_expect h]
  have hb := (s.longNormalizer_bounds h).1
  linarith

noncomputable def normalized (hB : 0 < B)
    (h : scalarCubeNormalizationThreshold (Fin q) M B T ≤ s.length) : NormalizedScalarCubeSource (Fin q) :=
  normalizedScalarCubeSourceOfThreshold (Fin q) s.length M s.modulus s.residue
    s.modulus_pos s.modulus_le s.weight B T hB s.weight_range s.weight_lipschitz s.weight_integral h

theorem normalized_sliceDensity (hB : 0 < B)
    (h : scalarCubeNormalizationThreshold (Fin q) M B T ≤ s.length) (x : s.Domain) :
    (s.normalized hB h).sliceDensity s.root x = s.sliceWeight x / s.longNormalizer h := rfl

theorem normalized_sliceWeights (hB : 0 < B)
    (h : scalarCubeNormalizationThreshold (Fin q) M B T ≤ s.length)
    (hmass : 0 < ∑ x, s.sliceWeight x) : (s.normalized hB h).sliceWeights s.root = s.law hmass := by
  have hZ : 0 < s.longNormalizer h := by have hb := (s.longNormalizer_bounds h).1; linarith
  exact FiniteProbabilityWeights.ofDensity_div_eq_ofPositiveWeights s.sliceWeight s.sliceWeight_nonneg
    hmass hZ ((s.normalized hB h).sliceDensity_mean_one s.root)

end SmoothCubeSlice

end Erdos3

end

section

namespace Erdos3

def supportedCubeInclusion {q : ℕ} {P Q : Set ℤ} (h : Q ⊆ P) :
    SupportedCube q Q ↪ SupportedCube q P where
  toFun x := ⟨x.val, fun ω => h (x.property ω)⟩
  inj' := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : SupportedCube q P => z.val) he)

def progressionCubeSlice (q m H : ℕ) (c : ℤ) : FiniteCubeSlice q where
  length := m * H
  root := c
  modulus := fun _ => m
  residue := progressionCubeResidues q m c

noncomputable def progressionCubeSliceEmbedding (q m H : ℕ) (c : ℤ) (hm : 0 < m)
    (P : Set ℤ) (hP : (integerProgressionSupport c (m : ℤ) H : Set ℤ) ⊆ P) :
    (progressionCubeSlice q m H c).Domain ↪ SupportedCube q P :=
  (progressionResidueSupportedCubeEquiv q m H c hm).symm.toEmbedding.trans (supportedCubeInclusion hP)

theorem progressionCubeSliceEmbedding_coordinates (q m H : ℕ) (c : ℤ) (hm : 0 < m)
    (P : Set ℤ) (hP : (integerProgressionSupport c (m : ℤ) H : Set ℤ) ⊆ P)
    (x : (progressionCubeSlice q m H c).Domain) :
    supportedCubeCoordinates (progressionCubeSliceEmbedding q m H c hm P hP x).val =
      (progressionCubeSlice q m H c).coordinates x := rfl

theorem progressionCubeSliceEmbedding_range (q m H : ℕ) (c : ℤ) (hm : 0 < m)
    (P : Set ℤ) [Finite P] (hP : (integerProgressionSupport c (m : ℤ) H : Set ℤ) ⊆ P) :
    finiteEmbeddingRange (progressionCubeSliceEmbedding q m H c hm P hP) =
      Finset.univ.filter (fun x => ∀ ω : Fin q → Bool,
        x.val.2 + cubeShift x.val.1 ω ∈ integerProgressionSupport c (m : ℤ) H) := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
    subst x
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((progressionResidueSupportedCubeEquiv q m H c hm).symm y).property⟩
  · intro hx
    let y : SupportedCube q (integerProgressionSupport c (m : ℤ) H : Set ℤ) :=
      ⟨x.val, (Finset.mem_filter.mp hx).2⟩
    refine Finset.mem_map.mpr ⟨progressionResidueSupportedCubeEquiv q m H c hm y, Finset.mem_univ _, ?_⟩
    change supportedCubeInclusion hP
      ((progressionResidueSupportedCubeEquiv q m H c hm).symm
        (progressionResidueSupportedCubeEquiv q m H c hm y)) = x
    rw [Equiv.symm_apply_apply]
    exact Subtype.ext rfl

end Erdos3

end

end OAI
