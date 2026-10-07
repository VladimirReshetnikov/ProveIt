import OAI.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedJointComparison
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [DecidableEq G] [Fintype X]
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

variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

include hR hσ in
theorem allocatedFixedPath_sliced_density_residue_comparison
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) z true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
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
    (q : ℕ) [NeZero q]
    (hsizeG : ∀ g, q ≤ HG g)
    (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1) (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (G → ZMod q) → (Input → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ rG r, LipschitzWith Kφ (φ rG r)) (hφone : ∀ rG r y, ‖φ rG r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (by have := hHG g; omega))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (by have := hH j; omega))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    let density := fixedSpatialKernelSliceOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) z (fun g => (cG g : ℝ) / S.value)
      (fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) h0 h1
      (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
        (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))) hB lower width sample
    ‖kernel.complexMean (fun x => active.complexMean (fun v =>
        φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S (embed x) u (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value)))) -
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ y, φ (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
            (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j) y
            ∂realDensityMeasure volume density))‖ ≤
      ((∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g := by
  classical
  intro lower width K kernel active embed density
  have hg (a : Active) (p : B a.val × Fin (degree a.val)) :=
    progression_slice_endpoint_geometry (c ⟨a,p⟩) S.positive (hstep _) (hH _)
      hδ (hsubset _) (hdense _)
  have hid (rG : G → ZMod q) (rA : Input → ZMod q) :
      (∫ y, φ rG rA y ∂realDensityMeasure volume density) =
        ∫ k, ∫ v, φ rG rA
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((cG g : ℝ) + (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) * k g) / S.value),
            allocatedOriginalSampleLiftMap B U basis S lower width sample v)
          ∂unitBoxMeasure Input ∂unitBoxMeasure G := by
    exact fixedSpatialKernelProgressionForecastDensity_iterated_test_integral B U basis hR hσ S
      e budget (S.value : ℝ) z cG (stepG : ℤ) HG
      (by exact_mod_cast hstepG) hHG h0 h1 hB lower width (half_pos hδ)
      (fun a p => (hg a p).2.1) (fun a p => (hg a p).1) sample hs
      (φ rG rA) (hφ rG rA).continuous.measurable (hφone rG rA)
  simp_rw [hid]
  exact allocatedFixedPath_sliced_joint_residue_comparison B U basis hR hσ S u z hz HG
    (fun g => by have := hHG g; omega) cG stepG hstepG hcontainedG sample hs ht hσbound
    step H c hstep hH hδ hsubset hdense q hsizeG hsmallG hsize hsmall hε hmesh
    hδone b hη A hA htail φ hφ hφone

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
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

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local instance slicedDensityCRTNeZero : NeZero Ncrt :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) z true).det ≠ 0)
    (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
    (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ) (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
    (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
    (q : ℕ) [NeZero q]
    (hsizeG : ∀ g, q ≤ HG g)
    (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1) (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    {Cidx : Type*} (selected : Cidx → Σ j : Fin m, Fin (n j))
    (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (physicalNoise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U basis S.value) j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (hp : ∀ l, (primes l).Prime)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    (hqN : q ∣ (∏ l, primes l ^ exponent l)) {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℂ) {Kφ : ℝ≥0}
    (htest : ∀ grid residue, LipschitzWith Kφ (test grid residue))
    (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1)

noncomputable def allocatedFixedPathSlicedForecastDensity : Domain → ℝ :=
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (stepG : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    fixedSpatialKernelSliceOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) z (fun g => (cG g : ℝ) / S.value)
      (fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) h0 h1
      (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
        (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))) hB lower width sample

noncomputable def allocatedFixedPathSlicedRationalFiniteMean : ℂ :=
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (lt_of_lt_of_le (by decide : 0 < 2) (hHG g)))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (lt_of_lt_of_le (by decide : 0 < 2) (hH j)))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    let shortLaw := allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let φ := fun u rG rA => test (forecastInactiveShortGrid B U basis S selected coeff u)
      (allocatedJointResidueOutput B U basis S base physicalNoise deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u rA))
    shortLaw.complexMean (fun u => kernel.complexMean (fun x => active.complexMean (fun v =>
        φ u (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (stepG : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S (embed x) u (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => ((c j : ℝ) + (stepG : ℝ) * (v j none : ℝ)) / S.value)))))

noncomputable def allocatedFixedPathSlicedRationalReferenceMean : ℂ :=
    let density := allocatedFixedPathSlicedForecastDensity B U basis S z HG hHG cG stepG hstepG e h0 h1 hB sample H c
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let poly := allocatedForecastPolynomial short base physicalNoise deck projection

    (∑' grid, 𝔼 residue : Out → ZMod Ncrt,
        ((rationalInactiveForecast
          (principalAffineIntervalLaw B degree (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP)
          (fun _ => crtPolynomialInputLaw primes exponent
            (fun l => padicValNat (primes l) stepG) hcoprime
            (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))
          (forecastInactiveFixedOutput B U basis S selected coeff xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) Ncrt)
          Ncrt gridVolume grid residue / gridVolume : ℝ) : ℂ) *
        ∫ y, test grid (fun j => ZMod.castHom hqN (ZMod q) (residue j)) y
          ∂realDensityMeasure volume density)

noncomputable def allocatedFixedPathSlicedResidueReferenceMean : ℂ :=
    let density := allocatedFixedPathSlicedForecastDensity B U basis S z HG hHG cG stepG hstepG e h0 h1 hB sample H c
    let shortLaw := allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let φ := fun u rG rA => test (forecastInactiveShortGrid B U basis S selected coeff u)
      (allocatedJointResidueOutput B U basis S base physicalNoise deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u rA))
    shortLaw.complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
      (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
      ∫ y, φ u (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
        (fun j => (c j : ZMod q) + (stepG : ZMod q) * rA j) y
        ∂realDensityMeasure volume density)))

include hR hσ hs hshort hp hV in
theorem allocatedFixedPathSlicedResidueReferenceMean_eq :
    allocatedFixedPathSlicedResidueReferenceMean B U basis S HP stepP cP hinsideP hHP z HG hHG cG stepG hstepG e h0 h1 hB sample H c q selected base physicalNoise deck projection test =
    allocatedFixedPathSlicedRationalReferenceMean B U basis S primes exponent HP stepP cP hinsideP hHP z HG hHG cG stepG hstepG e h0 h1 hB sample H c q selected xref base physicalNoise deck projection hcoprime hqN (gridVolume := gridVolume) test := by
  classical
  let density := allocatedFixedPathSlicedForecastDensity B U basis S z HG hHG cG stepG hstepG e h0 h1 hB sample H c
  have href := allocatedAffineFixedPath_joint_crtRationalForecast_reference
    B U basis S HP stepP cP hinsideP hHP primes exponent hR hσ selected hshort sample hs xref
    base physicalNoise deck projection stepG (Nat.ne_of_gt hstepG) (Sum.elim cG c)
    hp hcoprime hqN hV
    (fun grid residue => ∫ y, test grid residue y ∂realDensityMeasure volume density)
  dsimp only [allocatedFixedPathSlicedResidueReferenceMean, allocatedFixedPathSlicedRationalReferenceMean]
  exact href

noncomputable def allocatedFixedPathSlicedComparisonError : ℝ :=
    ((∑ j, (q : ℝ) / H j) +
      (2 * ((2 * scalarCubeGridBoundaryConstant Empty +
          (Kφ * allocatedOriginalSampleFullSliceLip B U basis S t : ℝ≥0) * 2) *
        ∑ j, (q : ℝ) / H j + (Kφ * allocatedOriginalSampleFullSliceLip B U basis S t : ℝ≥0) * ε) + 2 * η)) +
    (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g

local notation "comparisonError" => allocatedFixedPathSlicedComparisonError B U basis S HG (t := t) H q (ε := ε) (η := η) (Kφ := Kφ)

omit [∀ j, Fintype (E j)] in
include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh hδone b hη hA htail htest hbound hz in
theorem allocatedFixedPath_sliced_finite_reference_comparison :
    ‖allocatedFixedPathSlicedRationalFiniteMean B U basis S HP stepP cP hinsideP hHP z HG hHG cG stepG hcontainedG sample H c hH q selected base physicalNoise deck projection test -
    allocatedFixedPathSlicedResidueReferenceMean B U basis S HP stepP cP hinsideP hHP z HG hHG cG stepG hstepG e h0 h1 hB sample H c q selected base physicalNoise deck projection test‖ ≤
    comparisonError := by
  classical
  unfold allocatedFixedPathSlicedRationalFiniteMean allocatedFixedPathSlicedResidueReferenceMean
  dsimp only
  apply ((allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP).norm_complexMean_sub_le
    _ _ (fun _ => comparisonError) ?_).trans_eq
    ((allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP).mean_const _)
  intro u _
  exact allocatedFixedPath_sliced_density_residue_comparison B U basis hR hσ S u z hz HG hHG cG
    stepG hstepG hcontainedG e h0 h1 hB sample hs ht hσbound
    (fun _ => stepG) H c (fun _ => hstepG) hH hδ hsubset hdense q hsizeG hsmallG hsize hsmall
    hε hmesh hδone b hη A hA htail
    (fun rG rA => test
      (forecastInactiveShortGrid B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) u)
      (allocatedJointResidueOutput B U basis S base physicalNoise deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u rA)))
    (fun rG rA => htest _ _) (fun rG rA y => hbound _ _ y)

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh hδone b hη hA htail hshort hp hV htest hbound hz in
theorem allocatedFixedPath_sliced_rational_density_comparison :
    ‖allocatedFixedPathSlicedRationalFiniteMean B U basis S HP stepP cP hinsideP hHP z HG hHG cG stepG hcontainedG sample H c hH q selected base physicalNoise deck projection test -
    allocatedFixedPathSlicedRationalReferenceMean B U basis S primes exponent HP stepP cP hinsideP hHP z HG hHG cG stepG hstepG e h0 h1 hB sample H c q selected xref base physicalNoise deck projection hcoprime hqN (gridVolume := gridVolume) test‖ ≤ comparisonError := by
  rw [← allocatedFixedPathSlicedResidueReferenceMean_eq B U basis hR hσ S primes exponent
    HP stepP cP hinsideP hHP z HG hHG cG stepG hstepG e h0 h1 hB sample hs H c q selected
    hshort xref base physicalNoise deck projection hp hcoprime hqN hV test]
  exact allocatedFixedPath_sliced_finite_reference_comparison B U basis hR hσ S HP stepP cP
    hinsideP hHP z hz HG hHG cG stepG hstepG hcontainedG e h0 h1 hB sample hs ht hσbound H c hH
    hδ hsubset hdense q hsizeG hsmallG hsize hsmall hε hmesh hδone b hη A hA htail selected
    base physicalNoise deck projection test htest hbound

end Erdos3.VectorPolynomial

end

end OAI
