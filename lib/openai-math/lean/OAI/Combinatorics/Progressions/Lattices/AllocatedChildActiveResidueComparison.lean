import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleSlicedPerturbedRiemann

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

include hR hσ in
theorem allocatedOriginalSample_sliced_affine_residue_comparison (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) [NeZero q] (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (Input → ZMod q) → (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ r, LipschitzWith Kφ (φ r)) (hφone : ∀ r y, ‖φ r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
        (by have := hH j; omega))).complexMean
        (fun z => φ (fun j => ((c j + (step j : ℤ) * (z j none : ℤ) : ℤ) : ZMod q))
          (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
            sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      𝔼 r : Input → ZMod q,
        ∫ y, φ (fun j => (c j : ZMod q) + (step j : ZMod q) * r j)
          (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
          ∂unitBoxMeasure Input‖ ≤
      (∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η) := by
  classical
  intro lower width K
  let hHpos : ∀ j, 0 < H j := fun j => by have := hH j; omega
  let law := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j) (hHpos j))
  let residues := FiniteProbabilityWeights.uniform (Input → ZMod q)
  let conditioned := fun r : Input → ZMod q => FiniteProbabilityWeights.pi
    (fun j : Input => scalarCubeResidueWeights Empty (H j) q (hHpos j)
      (fun _ => q) (fun _ => r j) (fun _ => NeZero.pos q) (fun _ => le_rfl)
      (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))
  let F := allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample
  let value := fun (r : Input → ZMod q) (z : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) =>
    φ (fun j => (c j : ZMod q) + (step j : ZMod q) * r j)
      (F (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))
  let reference := fun r : Input → ZMod q =>
    ∫ y, φ (fun j => (c j : ZMod q) + (step j : ZMod q) * r j)
      (allocatedOriginalSampleLiftMap B U basis S lower width sample y) ∂unitBoxMeasure Input
  let error := 2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
    ∑ j, (q : ℝ) / H j + K * ε) + 2 * η
  have hc (r : Input → ZMod q) :
      ‖(conditioned r).complexMean (value r) - reference r‖ ≤ error := by
    exact allocatedOriginalSample_sliced_residue_perturbed_riemann B U basis hR hσ S x u
      sample hs ht hσbound step H (fun _ => q) c hstep hH hδ hsubset hdense
      (fun _ _ => q) (fun j _ => r j) (fun _ _ => NeZero.pos q) (fun _ _ => le_rfl)
      hsize hsmall hε hmesh hδone b hη A hA htail (φ _) (hφ _) (hφone _)
  have hm := integerScalarCubeWeights_empty_pi_uniform_residue_error_varying
    H q hHpos (NeZero.pos q) hsize value (fun r z => hφone _ _)
  have hm' : ‖law.complexMean (fun z => value (fun j => ((z j none : ℤ) : ZMod q)) z) -
      residues.complexMean (fun r => (conditioned r).complexMean (value r))‖ ≤
      ∑ j, (q : ℝ) / H j := by
    simpa only [law, residues, conditioned, FiniteProbabilityWeights.uniform_complexMean] using hm
  have ha : ‖residues.complexMean (fun r => (conditioned r).complexMean (value r)) -
      residues.complexMean reference‖ ≤ error :=
    (residues.norm_complexMean_sub_le _ _ (fun _ => error) (fun r _ => hc r)).trans_eq
      (residues.mean_const error)
  have he := (norm_sub_le_norm_sub_add_norm_sub
    (law.complexMean (fun z => value (fun j => ((z j none : ℤ) : ZMod q)) z))
    (residues.complexMean (fun r => (conditioned r).complexMean (value r)))
    (residues.complexMean reference)).trans
      (add_le_add hm' ha)
  simpa only [law, residues, conditioned, value, reference, error, F,
    FiniteProbabilityWeights.uniform_complexMean, Int.cast_add, Int.cast_mul, Int.cast_natCast] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

include hR hσ in
theorem allocatedOriginalSample_child_active_residue_comparison (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    {cutoff stride : ℕ} (hcutoff : cutoff ≤ S.value)
    (slice : ResidueBoxSlice
      (fun k : {k : LayerSamplerVariables G I n B // cutoff ≤
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) stride)
    (hstride : 0 < stride) {cost : ℝ} (hcost : 0 ≤ cost)
    (hlarge : 2 * Real.exp cost ≤ (S.value : ℝ))
    (hfraction : ∀ k, Real.exp (-cost) *
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℝ) ≤
        slice.length k)
    (q : ℕ) [NeZero q] (hsize : ∀ j : Input, q ≤ slice.length (allocatedChildNonshortCoordinate B U basis S hcutoff j.1 j.2.1 j.2.2))
    (hsmall : ∀ j : Input, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.length (allocatedChildNonshortCoordinate B U basis S hcutoff j.1 j.2.1 j.2.2)) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : (stride : ℝ) / S.value ≤ ε)
    (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η)
    (φ : (Input → ZMod q) → (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ r, LipschitzWith Kφ (φ r)) (hφone : ∀ r y, ‖φ r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => ((slice.start (allocatedChildNonshortCoordinate B U basis S hcutoff a p.1 p.2) : ℤ) : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (stride : ℝ) * ((slice.length (allocatedChildNonshortCoordinate B U basis S hcutoff a p.1 p.2) : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (slice.length (allocatedChildNonshortCoordinate B U basis S hcutoff j.1 j.2.1 j.2.2))
        (by
          have := (allocatedChildSlice_nonshort_geometry B U basis S hcutoff slice hstride hlarge hfraction j.1 j.2.1 j.2.2).1
          omega))).complexMean
        (fun z => φ (fun j => (((slice.start (allocatedChildNonshortCoordinate B U basis S hcutoff j.1 j.2.1 j.2.2) : ℤ) + (stride : ℤ) * (z j none : ℤ) : ℤ) : ZMod q))
          (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
            sample (fun j => (((slice.start (allocatedChildNonshortCoordinate B U basis S hcutoff j.1 j.2.1 j.2.2) : ℤ) : ℝ) + (stride : ℝ) * (z j none : ℝ)) / S.value))) -
      𝔼 r : Input → ZMod q,
        ∫ y, φ (fun j => ((slice.start (allocatedChildNonshortCoordinate B U basis S hcutoff j.1 j.2.1 j.2.2) : ℤ) : ZMod q) + (stride : ZMod q) * r j)
          (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
          ∂unitBoxMeasure Input‖ ≤
      (∑ j : Input, (q : ℝ) / slice.length (allocatedChildNonshortCoordinate B U basis S hcutoff j.1 j.2.1 j.2.2)) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j : Input, (q : ℝ) / slice.length (allocatedChildNonshortCoordinate B U basis S hcutoff j.1 j.2.1 j.2.2) + K * ε) + 2 * η) := by
  classical
  let coord := fun j : Input => allocatedChildNonshortCoordinate B U basis S hcutoff j.1 j.2.1 j.2.2
  let lengths := fun j : Input => slice.length (coord j)
  let starts := fun j : Input => (slice.start (coord j) : ℤ)
  have hg (j : Input) := allocatedChildSlice_nonshort_geometry B U basis S hcutoff
    slice hstride hlarge hfraction j.1 j.2.1 j.2.2
  have hsubset (j : Input) : integerProgressionSupport (starts j) (stride : ℤ) (lengths j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ) := by
    simpa only [coord, starts, lengths, allocatedChildNonshortCoordinate_side] using slice.coordinate_progression_subset (coord j)
  have hdense (j : Input) : Real.exp (-cost) * (S.value : ℝ) ≤
      ((integerProgressionSupport (starts j) (stride : ℤ) (lengths j)).card : ℝ) := by
    rw [card_integerProgressionSupport _ _ _ hstride]
    simpa only [coord, starts, lengths, allocatedChildNonshortCoordinate_side] using hfraction (coord j)
  exact allocatedOriginalSample_sliced_affine_residue_comparison B U basis hR hσ S x u
    sample hs ht hσbound (fun _ => stride) lengths starts (fun _ => hstride) (fun j => (hg j).1)
    (Real.exp_pos (-cost)) hsubset hdense q hsize hsmall hε (fun _ => hmesh)
    (by exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hcost)) b hη A hA htail φ hφ hφone

end Erdos3.VectorPolynomial

end

end OAI
