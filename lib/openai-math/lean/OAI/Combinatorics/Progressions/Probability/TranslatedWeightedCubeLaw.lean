import OAI.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem normalizedScalarCubeSourceOfWeight_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hZ : 1 / 2 ≤ (scalarCubeResidueWeights I L M hL m res hm hmM hsize).mean
      (fun z => w (fun i => (z i : ℝ) / L))) (f : IntegerScalarCubeBox I L → ℝ) :
    let p := scalarCubeResidueWeights I L M hL m res hm hmM hsize
    (normalizedScalarCubeSourceOfWeight I L M hL m res hm hmM hsize w B T hB hw hLip hZ).source.mean f =
      p.mean (fun z => w (fun i => (z i : ℝ) / L) * f z) /
        p.mean (fun z => w (fun i => (z i : ℝ) / L)) := by
  let p := scalarCubeResidueWeights I L M hL m res hm hmM hsize
  change (∑ z, (p.weight z * (w (fun i => (z i : ℝ) / L) /
    p.mean (fun z => w (fun i => (z i : ℝ) / L)))) * f z) = _
  simp only [FiniteProbabilityWeights.mean, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem normalizedScalarCubeSourceOfWeight_primitive (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hZ : 1 / 2 ≤ (scalarCubeResidueWeights I L M hL m res hm hmM hsize).mean
      (fun z => w (fun i => (z i : ℝ) / L))) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget
      (normalizedScalarCubeSourceOfWeight I L M hL m res hm hmM hsize w B T hB hw hLip hZ) A
      (scalarCubePrimitiveEnvelope I A (2 * B) (2 * T) M) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A (2 * B) (2 * T) M le_rfl le_rfl le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem shiftScalarCube_neg_shift {I : Type*} (c : ℤ) (x : Option I → ℤ) :
    shiftScalarCube (-c) (shiftScalarCube c x) = x := by
  funext i
  cases i <;> simp [shiftScalarCube]

noncomputable def translatedCubeWeight {I : Type*} (L : ℕ) (c : ℤ) (w : (Option I → ℝ) → ℝ)
    (y : Option I → ℤ) : ℝ := w (fun i => (shiftScalarCube (-c) y i : ℝ) / L)

theorem scalarCubeResidueWeights_translated_mean (q L M : ℕ) (c : ℤ) (hL : 0 < L)
    (m : Option (Fin q) → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card (Fin q) + 1) * M ≤ L)
    (f : (Option (Fin q) → ℤ) → ℝ) :
    (scalarCubeResidueWeights (Fin q) L M hL m (shiftScalarCubeResidues c m res) hm hmM hsize).mean
      (fun x => f (shiftScalarCube c (fun i => (x i : ℤ)))) =
        𝔼 p : TranslatedResidueSupportedCube q L c m res, f (supportedCubeCoordinates p.val.val) := by
  exact (normalizedUniformCubeSource_mean (Fin q) L M hL m (shiftScalarCubeResidues c m res) hm hmM hsize _).symm.trans
    (normalizedUniformCubeSource_translated_mean q L M c hL m res hm hmM hsize f)

theorem normalizedWeightedCube_translated_mean (q L M : ℕ) (c : ℤ) (hL : 0 < L)
    (m : Option (Fin q) → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card (Fin q) + 1) * M ≤ L)
    (w : (Option (Fin q) → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hZ : 1 / 2 ≤ (scalarCubeResidueWeights (Fin q) L M hL m
      (shiftScalarCubeResidues c m res) hm hmM hsize).mean (fun z => w (fun i => (z i : ℝ) / L)))
    (f : (Option (Fin q) → ℤ) → ℝ) :
    (normalizedScalarCubeSourceOfWeight (Fin q) L M hL m (shiftScalarCubeResidues c m res) hm hmM hsize
      w B T hB hw hLip hZ).source.mean (fun x => f (shiftScalarCube c (fun i => (x i : ℤ)))) =
        (𝔼 p : TranslatedResidueSupportedCube q L c m res,
          translatedCubeWeight L c w (supportedCubeCoordinates p.val.val) * f (supportedCubeCoordinates p.val.val)) /
        (𝔼 p : TranslatedResidueSupportedCube q L c m res,
          translatedCubeWeight L c w (supportedCubeCoordinates p.val.val)) := by
  apply (normalizedScalarCubeSourceOfWeight_mean (Fin q) L M hL m (shiftScalarCubeResidues c m res)
    hm hmM hsize w B T hB hw hLip hZ (fun x => f (shiftScalarCube c (fun i => (x i : ℤ))))).trans
  congr 1
  · have he := scalarCubeResidueWeights_translated_mean q L M c hL m res hm hmM hsize
      (fun y => translatedCubeWeight L c w y * f y)
    simpa only [translatedCubeWeight, shiftScalarCube_neg_shift] using he
  · have he := scalarCubeResidueWeights_translated_mean q L M c hL m res hm hmM hsize
      (translatedCubeWeight L c w)
    simpa only [translatedCubeWeight, shiftScalarCube_neg_shift] using he

end Erdos3

end

end OAI
