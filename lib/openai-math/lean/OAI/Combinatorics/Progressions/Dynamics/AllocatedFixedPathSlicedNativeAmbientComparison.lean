import OAI.Combinatorics.Progressions.Dynamics.AllocatedFixedPathAmbientUniformPrecision
import OAI.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedSourceErrorBudget
import OAI.Combinatorics.Progressions.Geometry.FixedSpatialSliceNativeAmbientRationalComparison
import OAI.Combinatorics.Progressions.Geometry.ProgressionEndpointUnitBox

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedFixedPath_sliced_kernel_geometry
    (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ)) :
    (∀ g, 0 ≤ (cG g : ℝ) / S.value) ∧
    (∀ g, 0 ≤ (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) ∧
    (∀ g, (cG g : ℝ) / S.value +
      (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value ≤ 1) ∧
    (∀ g, 0 < (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) := by
  have hg (g : G) := progression_slice_endpoint_unit_box (cG g) S.positive
    hstepG (by have := hHG g; omega) (hcontainedG g)
  refine ⟨fun g => (hg g).1, fun g => (hg g).2.1, fun g => (hg g).2.2, ?_⟩
  intro g
  simpa only [Int.cast_natCast] using fixedSpatialKernelProgression_width_pos S.positive
    (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g)

local notation "Active" => {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))

theorem allocatedFixedPath_sliced_principal_geometry
    (stepG : ℕ) (hstepG : 0 < stepG) (H : Input → ℕ) (c : Input → ℤ)
    (hH : ∀ j, 2 ≤ H j) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ)) :
    let lower := fun (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) =>
      (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) =>
      (stepG : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    (∀ a p, δ / 2 ≤ width a p) ∧ (∀ a p, 0 ≤ lower a p) ∧
      (∀ a p, |lower a p| + |width a p| ≤ 1) := by
  intro lower width
  have hg (j : Input) := progression_slice_endpoint_geometry (c j) S.positive hstepG
    (hH j) hδ (hsubset j) (hdense j)
  exact ⟨fun a p => (hg ⟨a, p⟩).2.1, fun a p => (hg ⟨a, p⟩).1,
    fun a p => (hg ⟨a, p⟩).2.2.1⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
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
local instance slicedPhysicalDensityCRTNeZero : NeZero Ncrt :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
variable {Cidx : Type*}
variable (selected : Cidx → Σ j : Fin m, Fin (n j))
variable (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U basis S.value) j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ}
variable (hV : gridVolume ≠ 0)
variable (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℂ)
variable {Kφ : ℝ≥0}
variable (htest : ∀ grid residue, LipschitzWith Kφ (test grid residue))
variable (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1)

noncomputable def allocatedSlicedPhysicalForecastDensity : Domain → ℝ :=
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (stepG : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    fixedSpatialKernelSliceOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) (fun g => (cG g : ℝ) / S.value)
      (fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) h0 h1
      (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
        (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))) hB lower width sample

noncomputable def allocatedSlicedPhysicalSourceMean : ℂ :=
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (lt_of_lt_of_le (by decide : 0 < 2) (hHG g)))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (lt_of_lt_of_le (by decide : 0 < 2) (hH j)))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    let activeEmbed := allocatedActiveContainedProgression B U basis S (fun _ => stepG) H c hsubset
    let joined := fun u v => principalAxisJoin short u (activeEmbed v)
    let shortLaw := allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let φ := fun u rG rA => test (forecastInactiveShortGrid B U basis S selected coeff u)
      (allocatedJointResidueOutput B U basis S base integerFrame deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u rA))
    shortLaw.complexMean (fun u => kernel.complexMean (fun x => active.complexMean (fun v =>
        φ u (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (stepG : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          ((fun o : Σ _ : X, Unit ⊕ Empty =>
              (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
                (embed x) (joined u v)) integerFrame o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8)),
            (fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
              (allocatedOriginalSamplePhysicalMixedValue B U basis S sample (embed x) (joined u v))
                o.1.val)))))

noncomputable def allocatedSlicedPhysicalRationalMean (g : Domain → ℝ) : ℂ :=
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let poly := allocatedForecastPolynomial short base integerFrame deck projection
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
          ∂realDensityMeasure volume g)

noncomputable def allocatedSlicedPhysicalResidueMean (g : Domain → ℝ) : ℂ :=
    let shortLaw := allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let φ := fun u rG rA => test (forecastInactiveShortGrid B U basis S selected coeff u)
      (allocatedJointResidueOutput B U basis S base integerFrame deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u rA))
    shortLaw.complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ y, φ u (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
            (fun j => (c j : ZMod q) + (stepG : ZMod q) * rA j) y
            ∂realDensityMeasure volume g)))

noncomputable def allocatedSlicedPhysicalComparisonError : ℝ :=
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ((∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g + (Kφ : ℝ) * ξ

local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "sourceMean" => allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
  τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base deck projection test
local notation "finiteReference" => allocatedSlicedPhysicalResidueMean B U basis S HP stepP cP hinsideP hHP
  integerFrame cG stepG sample c q selected base deck projection test actualDensity
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base deck projection
  hcoprime hqN (gridVolume := gridVolume) test actualDensity
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Kφ)

omit [∀ j, Fintype (E j)] in
include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail htest hbound hτ hξ hbox hframe in
theorem allocatedSlicedPhysicalSourceMean_residue_comparison :
    ‖sourceMean - finiteReference‖ ≤ comparisonError := by
  classical
  unfold allocatedSlicedPhysicalSourceMean allocatedSlicedPhysicalResidueMean
  dsimp only
  apply ((allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP).norm_complexMean_sub_le
    _ _ (fun _ => comparisonError) ?_).trans_eq
      ((allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP).mean_const _)
  intro u _
  exact allocatedFixedPath_sliced_physical_density_residue_comparison B U basis hR hσ S u
    τ ξ hτ hξ box hbox integerFrame hframe HG hHG cG
    stepG hstepG hcontainedG e h0 h1 hB sample hs ht hσbound
    (fun _ => stepG) H c (fun _ => hstepG) hH hδ hsubset hdense q hsizeG hsmallG hsize hsmall
    hε hmesh hδone b hη A hA htail
    (fun uG uA => test
      (forecastInactiveShortGrid B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) u)
      (allocatedJointResidueOutput B U basis S base integerFrame deck projection q uG
        (allocatedPrincipalResidueJoin B U basis S q u uA)))
    (fun rG rA => htest _ _) (fun rG rA y => hbound _ _ y)

include hR hσ hs hshort hp hV in
theorem allocatedSlicedPhysicalResidueMean_eq_rationalMean :
    finiteReference = rationalReference := by
  exact allocatedAffineFixedPath_joint_crtRationalForecast_reference
    B U basis S HP stepP cP hinsideP hHP primes exponent hR hσ selected hshort sample hs xref
    base integerFrame deck projection stepG (Nat.ne_of_gt hstepG) (Sum.elim cG c)
    hp hcoprime hqN hV
    (fun grid residue => ∫ y, test grid residue y ∂realDensityMeasure volume actualDensity)

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hshort hp hV htest hbound hτ hξ hbox hframe in
theorem allocatedFixedPath_sliced_physical_rational_density_comparison :
    ‖sourceMean - rationalReference‖ ≤ comparisonError := by
  rw [← allocatedSlicedPhysicalResidueMean_eq_rationalMean B U basis hR hσ S primes exponent
    HP stepP cP hinsideP hHP τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample hs
    H c q selected hshort xref base deck projection hp hcoprime hqN hV test]
  exact allocatedSlicedPhysicalSourceMean_residue_comparison B U basis hR hσ S
    HP stepP cP hinsideP hHP τ ξ hτ hξ box hbox integerFrame hframe HG hHG cG stepG hstepG
    hcontainedG e h0 h1 hB sample hs ht hσbound H c hH hδ hsubset hdense q hsizeG hsmallG
    hsize hsmall hε hmesh hδone b hη A hA htail selected base deck projection test htest hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
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
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Grid" => AllocatedShortIntegerAxis U basis S.value →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

local instance slicedNativeSourceMeanCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (hbox : ∀ a, 0 < box a) {τ : ℝ} (hτ : τ ≠ 0)
variable (q : ℕ) [NeZero q] (hm : 0 < m)
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)
variable (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ) (stepG : ℕ)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))

noncomputable def allocatedSlicedNativeEvalMean : ℂ :=
  let kernel := FiniteProbabilityWeights.pi (fun g =>
    integerScalarCubeWeights Empty (HG g) (lt_of_lt_of_le (by decide : 0 < 2) (hHG g)))
  let active := FiniteProbabilityWeights.pi (fun j : Input =>
    integerScalarCubeWeights Empty (H j) (lt_of_lt_of_le (by decide : 0 < 2) (hH j)))
  let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
    containedProgressionCubeMap Empty S.value (HG g) stepG (cG g)
      S.positive (hcontainedG g) (x g)
  let joined := fun u v => principalAxisJoin short u
    (allocatedActiveContainedProgression B U basis S (fun _ => stepG) H c hsubset v)
  let shortLaw := allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP
  shortLaw.complexMean (fun u => kernel.complexMean (fun x => active.complexMean (fun v =>
    W.eval box nativePoly (fun a => base a + integerPhysicalSite
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) (embed x) (joined u v)) integerFrame a))))

include hs hbox hτ hdegree hbase hsmallChart hread in

theorem allocatedSlicedPhysicalSourceMean_eq_native :
    allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
      τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base
      (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)
      (W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
        (fun a => (base a : ℝ) / box a) τ) =
      allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
        HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset := by
  unfold allocatedSlicedPhysicalSourceMean allocatedSlicedNativeEvalMean
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro u _
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro x hx
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro v hv
  exact allocatedFixedPath_sliced_recovered_native_atom B U basis hR hσ S hb o bW W
    sample hs base integerFrame box hbox hτ q hm hperiod hcover nativePoly hmem hdegree
    hbase hsmallChart read hread HG
    (fun g => lt_of_lt_of_le (by decide : 0 < 2) (hHG g)) cG stepG hcontainedG
    (fun _ => stepG) H c (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset u x hx v hv

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

noncomputable def allocatedFixedPathSlicedAmbientFloorLog
    (d : ℕ) (D P V cost E Pg PR : ℝ) : ℝ :=
  max (D + 2 * P + V + cost + E + 32)
    (forecastJointGridSamplerLog d Pg (E + 4) V PR + 1)

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedSlicedPhysicalComparisonError_eq_sourceError
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (ξ : ℝ) (HG : G → ℕ)
    (H : PrincipalTupleIndex
      (fun a : {a // ¬allocatedShortAxis (I := I) U basis S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → ℕ)
    (q : ℕ) {t ε η : ℝ} (Kφ : ℝ≥0) :
    allocatedSlicedPhysicalComparisonError B U basis S ξ HG (t := t) H q
      (ε := ε) (η := η) (Kφ := Kφ) =
    fixedPathSlicedSourceError (∑ j, (q : ℝ) / H j) (∑ g, (q : ℝ) / HG g)
      (scalarCubeGridBoundaryConstant Empty)
      ((Kφ : ℝ) * allocatedOriginalSampleFullSliceLip B U basis S t) Kφ ε η ξ := by
  simp only [allocatedSlicedPhysicalComparisonError, fixedPathSlicedSourceError, NNReal.coe_mul]
  ring

theorem exists_allocatedFixedPathSlicedUniformPrecision
    (d : ℕ) {D P V cost E Pg PR Q : ℝ}
    (hD : 0 ≤ D) (hP : 2 ≤ P) (hV : 0 ≤ V) (hcost : 0 ≤ cost) (hE : 0 ≤ E)
    (hPg : 0 ≤ Pg) (hPR : 0 ≤ PR) (hQ : 0 ≤ Q)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (hG : (Fintype.card G : ℝ) ≤ D)
    (hLift : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) * m ≤ P)
    (A : ℝ≥0) (hAP : (A : ℝ) ≤ Real.exp P) :
    let F := 2 * P + (E + 4) + 14
    let η := Real.exp (-F)
    let Qσ := fixedPathSlicedPerturbationLog D (D + P + 4) (cost + 1) F m
    let t := Real.exp (-Qσ)
    let δnative := Real.exp (-(E + 8))
    let Eprec := Q + E + 8
    let cutoff := forecastJointGridCutoff Pg (E + 4)
    let δgrid := forecastJointGridMesh d Pg (E + 4)
    0 < δnative ∧ δnative ≤ 1 ∧ 0 ≤ Eprec ∧
    1 ≤ cutoff ∧ (cutoff : ℝ) ≤ Real.exp (Pg + E + 9) ∧
    0 < δgrid ∧ δgrid ≤ 1 ∧ 0 < t ∧ t ≤ 1 ∧ 0 < η ∧ η ≤ 1 ∧
    ∃ Lmin : ℕ, 0 < Lmin ∧
      (Lmin : ℝ) ≤ Real.exp (allocatedFixedPathSlicedAmbientFloorLog d D P V cost E Pg PR) ∧
      ∀ {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ),
      let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
      let Input := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
        (fun a => layerSamplerDegree I n a.val)
      |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
        slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card {a // active a})
          m 1 (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η ∧
      ∀ (HP : Input → ℕ) (HG : G → ℕ) (Kφ : ℝ≥0), (Kφ : ℝ) ≤ Real.exp P →
      ∀ {q : ℕ}, 0 < q → (q : ℝ) ≤ Real.exp V → Lmin ≤ S.value →
      (∀ i, Real.exp (-cost) * S.value ≤ (HP i : ℝ)) →
      (∀ i, Real.exp (-cost) * S.value ≤ (HG i : ℝ)) →
      ∀ {ξ : ℝ}, 0 ≤ ξ → ξ ≤ η →
      forecastJointGridSamplerFloor d Pg (E + 4) V PR ≤ S.value ∧
      (∀ i, 2 ≤ HP i ∧ q ≤ HP i ∧
        scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HP i) < 1) ∧
      (∀ i, 2 ≤ HG i ∧ q ≤ HG i ∧
        scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG i) < 1) ∧
      ∀ {dout dj dc : ℕ}, dout ≤ d → dj ≤ d → dc ≤ d →
      ∀ {Dgrid Lgrid Cgrid Kgrid Mmass : ℝ},
      0 ≤ Dgrid → 0 ≤ Lgrid → 0 ≤ Cgrid → 0 ≤ Kgrid →
      Dgrid ≤ Real.exp Pg → Lgrid ≤ Real.exp Pg → Cgrid ≤ Real.exp Pg → Kgrid ≤ Real.exp Pg →
      Mmass ≤ Real.exp Q →
      allocatedSlicedPhysicalComparisonError B U basis S ξ HG (t := t) HP q
        (ε := 2 * Real.exp cost / S.value) (η := η) (Kφ := Kφ) +
        ((2 * δnative + Mmass * Real.exp (-Eprec)) +
          forecastJointGridError dout dj dc cutoff Dgrid Lgrid Cgrid Kgrid δgrid) ≤ Real.exp (-E) := by
  intro F η Qσ t δnative Eprec cutoff δgrid
  have hE4 : 0 ≤ E + 4 := by linarith
  obtain ⟨hLsrc, hsrcBound, ht, ht1, hη, hη1, hsource⟩ :=
    allocatedFixedPathSlicedSourceErrorBudget (G := G) B U basis hD hP hV hcost hE4
      hInput hAxis hG hLift A hAP
  let Lsrc := fixedPathSlicedGridMeshFloor D 4 V cost F
  let Lgrid := forecastJointGridSamplerFloor d Pg (E + 4) V PR
  have hgrid := forecastJointGridErrorBudget d hPg hE4
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith),
    by dsimp only [Eprec]; linarith, hgrid.1, ?_, hgrid.2.2.1, hgrid.2.2.2.1,
    ht, ht1, hη, hη1, max Lsrc Lgrid, hLsrc.trans_le (le_max_left _ _), ?_, ?_⟩
  · convert hgrid.2.1 using 1
    congr 1
    ring
  · rw [Nat.cast_max]
    apply max_le
    · apply hsrcBound.trans (Real.exp_le_exp.mpr _)
      apply le_trans _ (le_max_left _ _)
      linarith
    · exact (forecastJointGridSamplerFloor_le_exp d hPg hE4 hV hPR).trans
        (Real.exp_le_exp.mpr (le_max_right _ _))
  intro R σ S active Input
  refine ⟨(hsource S).1, ?_⟩
  intro HP HG Kφ hKφ q hq0 hq hfloor hHP hHG ξ hξ0 hξ
  have hsrcFloor : Lsrc ≤ S.value := (le_max_left _ _).trans hfloor
  have hgridFloor : Lgrid ≤ S.value := (le_max_right _ _).trans hfloor
  obtain ⟨hPmesh, hGmesh, herror⟩ := (hsource S).2 HP HG Kφ hKφ hq0 hq hsrcFloor hHP hHG hξ0 hξ
  refine ⟨hgridFloor, hPmesh, hGmesh, ?_⟩
  intro dout dj dc hdout hdj hdc Dgrid Lgrid Cgrid Kgrid Mmass hDg hLg hCg hKg hDexp hLexp hCexp hKexp hM
  rw [allocatedSlicedPhysicalComparisonError_eq_sourceError]
  simpa only [η, F, t, Qσ, δnative, Eprec, cutoff, δgrid, add_assoc] using
    fixedPathSlicedAmbientScalarPrecision_error dout dj dc d hdout hdj hdc hPg hE
      herror hM hDg hLg hCg hKg hDexp hLexp hCexp hKexp hgrid.2.2.1.le le_rfl

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
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
local instance slicedRecoveredNativeCRTNeZero : NeZero Ncrt :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "nativeTest" => W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
  (fun a => (base a : ℝ) / box a) τ
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample
local notation "sourceMean" => allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
  τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base
  (allocatedReadDeck read) projection nativeTest
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base
  (allocatedReadDeck read) projection hcoprime hqN (gridVolume := gridVolume) nativeTest actualDensity
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Knative)

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hp hV hτ hξ hbox hframe in
theorem allocatedFixedPath_sliced_native_test_rational_comparison :
    ‖sourceMean - rationalReference‖ ≤ comparisonError := by
  have htest := W.forecastShortGridTest_bounds U basis S.value hb o bW R q hm hperiod hcover
    (fun a => (base a : ℝ) / box a) τ
  exact allocatedFixedPath_sliced_physical_rational_density_comparison B U basis hR hσ S primes exponent
    HP stepP cP hinsideP hHP τ ξ hτ hξ box hbox integerFrame hframe HG hHG cG stepG hstepG
    hcontainedG e h0 h1 hB sample hs ht hσbound H c hH hδ hsubset hdense q hsizeG hsmallG
    hsize hsmall hε hmesh hδone b hη A hA htail selected
    (allocatedShortIntegerSelection_small U basis S.value) xref base (allocatedReadDeck read)
    projection hp hcoprime hqN hV nativeTest (fun grid residue => (htest grid residue).2)
    (fun grid residue => (htest grid residue).1)

local instance slicedNativeRecoveredCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hp hV hτ hξ hbox hframe hmem hdegree hbase hsmallChart hread in

theorem allocatedFixedPath_sliced_recovered_native_rational_comparison :
    ‖allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
        HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset -
      rationalReference‖ ≤ comparisonError := by
  have he := allocatedFixedPath_sliced_native_test_rational_comparison B U basis hR hσ S
    primes exponent HP stepP cP hinsideP hHP τ ξ hτ hξ box hbox integerFrame hframe HG hHG cG
    stepG hstepG hcontainedG e h0 h1 hB sample hs ht hσbound H c hH hδ hsubset hdense q
    hsizeG hsmallG hsize hsmall hε hmesh hδone b hη A hA htail hb o bW W hm hperiod hcover
    xref base read hp hcoprime hqN hV
  rw [allocatedSlicedPhysicalSourceMean_eq_native B U basis hR hσ S hb o bW W sample hs
    base integerFrame box hbox hτ.ne' q hm hperiod hcover nativePoly hmem hdegree
    hbase hsmallChart read hread HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG
    H c hH hsubset] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
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
local instance slicedAmbientNativeCRTNeZero : NeZero Ncrt :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "nativeTest" => W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
  (fun a => (base a : ℝ) / box a) τ
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample
local notation "sourceMean" => allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
  τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base
  (allocatedReadDeck read) projection nativeTest
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base
  (allocatedReadDeck read) projection hcoprime hqN (gridVolume := gridVolume) nativeTest actualDensity
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Knative)

local instance slicedAmbientRecoveredCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

local notation "actualLaw" => principalAffineIntervalLaw B degree
  (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP
local notation "actualActive" => (fun _ : Original => crtPolynomialInputLaw primes exponent
  (fun l => padicValNat (primes l) stepG) hcoprime
  (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))
local notation "actualOutput" => (fun v : Original => integerLongPolynomialOutput
  (allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection)
  (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) Ncrt)
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I)
  U basis R S.value gridVolume τ : ℝ) : ℂ)
local notation "actualTarget" => forecastLawDensityPhysicalTarget B U basis S actualLaw
  actualDensity selected sample xref actualActive actualOutput Ncrt gridVolume
  base box τ o hb bW

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
variable (radius : ℝ≥0) (hradius0 : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
variable (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
variable (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
  chartCap j * ‖v‖)
variable (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
  (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ box i ≤ box i)
variable (htrimbase : base ∈ trimmedIntegerBox box (spatialTrimMargin τ box))
variable (hVpos : 0 < gridVolume)
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((forecastGeometricJacobian (X := X) (I := I) U basis R S.value gridVolume τ : ℝ) : ℂ) * (forecastLawDensityPhysicalTarget B U basis S (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP) (allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c) (allocatedShortIntegerSelection U basis S.value) sample xref (fun _ : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => crtPolynomialInputLaw primes exponent (fun l => padicValNat (primes l) stepG) hcoprime (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l)))) (fun v : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => integerLongPolynomialOutput (allocatedForecastPolynomial (allocatedShortAxis (I := I) U basis S.value) base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) (∏ l, primes l ^ exponent l)) (∏ l, primes l ^ exponent l) gridVolume base box τ o hb bW) poly hpoly u - ∑ i, nativeCoeff i * (F i).eval box poly u‖ ≤ δnative)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hX : (Fintype.card X : ℝ) ≤ Pambient)
variable (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hlarge : ∀ i, Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (box i : ℝ))
variable (hRrank : Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ))
  Rrank (U j) (nativePoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
variable (hPdecay : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) + 2 : ℕ) : ℝ) ≤ Pdecay)
variable (hdecay : ∀ i (χ : AddChar ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod (∏ l, primes l ^ exponent l)) ℂ),
  ‖finiteImageCharacteristic ((fun _ : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => crtPolynomialInputLaw primes exponent (fun l => padicValNat (primes l) stepG) hcoprime (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l)))) i) (fun x j => ((fun v : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => integerLongPolynomialOutput (allocatedForecastPolynomial (allocatedShortAxis (I := I) U basis S.value) base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) (∏ l, primes l ^ exponent l)) i x j : ZMod (∏ l, primes l ^ exponent l))) χ‖ ≤
    D * (orderOf χ : ℝ) ^ (-Pdecay))
variable (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U basis R S.value box τ j ≤ δgrid)

noncomputable def allocatedSlicedPhysicalAmbientMean : ℂ :=
  𝔼 u ∈ integerBox box, W.eval box nativePoly u * (κ * actualTarget nativePoly hmem u)

noncomputable def allocatedSlicedPhysicalAmbientGridError : ℝ :=
  let lowerG := fun g => (cG g : ℝ) / S.value
  let widthG := fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value
  let frame := allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame
  let hwGne := fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
    (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))
  let slicedFrame := fixedSpatialKernelSliceFrame budget (S.value : ℝ) frame lowerG widthG
  let h0slice := fixedSpatialKernelBlock_slice_det_ne_zero e budget (S.value : ℝ) frame
    lowerG widthG false h0 hwGne
  let h1slice := fixedSpatialKernelBlock_slice_det_ne_zero e budget (S.value : ℝ) frame
    lowerG widthG true h1 hwGne
  let hδP : 0 < δ / 2 := div_pos hδ (by norm_num)
  let Cgrid := fixedSpatialOriginalForecastCap B
    (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ) slicedFrame true h1slice) hδP
  let Lgrid := fixedSpatialOriginalForecastLip B
    (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ) slicedFrame false h0slice)
    (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ) slicedFrame true h1slice) hδP
  forecastJointGridError (Fintype.card Out)
    (Fintype.card (X ⊕ AllocatedActiveIntegerAxis U basis S.value))
    (Fintype.card (Σ j, I j)) cutoff D Lgrid Cgrid Knative δgrid

include hR hσ hs hτ hξ hbox hframe hcontainedG hH hδ hsubset hdense ν hlattice hcompact hσ1
  hradius0 hradius3 hradius hchartCap hchart hchartBudget hmargin htrimbase hVpos
  happrox hdegree hPambient hEprec hX hdim hLip hcoverF hmodF hmass hlarge hRrank hrank
  hcutoff hD hPdecay hdecay hδgrid hδgrid1 hgridmesh in

theorem allocatedFixedPath_sliced_ambient_rational_comparison :
    ‖(𝔼 u ∈ integerBox box, W.eval box nativePoly u *
        (κ * actualTarget nativePoly hmem u)) - rationalReference‖ ≤
      (2 * δnative + M * Real.exp (-Eprec)) +
        allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := basis) (S := S)
          (E := E) (τ := τ) (ξ := ξ) (box := box) (integerFrame := integerFrame)
          (HG := HG) (hHG := hHG) (cG := cG) (stepG := stepG) (hstepG := hstepG)
          (e := e) (h0 := h0) (h1 := h1) (hδ := hδ) (o := o) (Lip := Lip)
          (cutoff := cutoff) (D := D) (δgrid := δgrid) := by
  let lowerP := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
    (c ⟨a, p⟩ : ℝ) / S.value
  let widthP := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
    (stepG : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
  let lowerG := fun g => (cG g : ℝ) / S.value
  let widthG := fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value
  let frame := allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame
  have hwGne : ∀ g, widthG g ≠ 0 := fun g => ne_of_gt
    (fixedSpatialKernelProgression_width_pos S.positive
      (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))
  have hδP : 0 < δ / 2 := div_pos hδ (by norm_num)
  have hPgeo := allocatedFixedPath_sliced_principal_geometry B U basis S
    stepG hstepG H c hH hδ hsubset hdense
  have hGgeo := allocatedFixedPath_sliced_kernel_geometry B U basis S
    HG hHG cG stepG hstepG hcontainedG
  have hframegeo := allocatedFixedPathKernelFrame_geometry B U basis S
    hτ hξ box hbox integerFrame hframe
  have hcomparison := fixedSpatialSliceNativeAmbientRationalMean_comparison B U basis hR hσ S
    actualLaw lowerP widthP sample xref actualActive actualOutput Ncrt gridVolume base box τ
    o hb bW W ν e budget (S.value : ℝ) frame lowerG widthG hwGne h0 h1 hB
    hs hδP hPgeo.1 hPgeo.2.1 hPgeo.2.2 hGgeo.1 hGgeo.2.1 hGgeo.2.2.1
    hσ1 radius hradius0 hradius3 hradius chartCap hchartCap hchart hchartBudget
    hframegeo.1 hframegeo.2.1 hframegeo.2.2.1 hframegeo.2.2.2 hτ hmargin htrimbase
    q hqN hm hperiod hcover hVpos F nativeCoeff δnative happrox nativePoly hdegree hmem
    hPambient hEprec hX hdim hLip hcoverF hmodF hmass hlarge hRrank hrank
    cutoff hcutoff hD hPdecay hdecay hδgrid hδgrid1 hgridmesh
  exact hcomparison

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
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
local instance slicedCompleteNativeCRTNeZero : NeZero Ncrt :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "nativeTest" => W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
  (fun a => (base a : ℝ) / box a) τ
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample
local notation "sourceMean" => allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
  τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base
  (allocatedReadDeck read) projection nativeTest
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base
  (allocatedReadDeck read) projection hcoprime hqN (gridVolume := gridVolume) nativeTest actualDensity
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Knative)

local instance slicedCompleteRecoveredCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

local notation "actualLaw" => principalAffineIntervalLaw B degree
  (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP
local notation "actualActive" => (fun _ : Original => crtPolynomialInputLaw primes exponent
  (fun l => padicValNat (primes l) stepG) hcoprime
  (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))
local notation "actualOutput" => (fun v : Original => integerLongPolynomialOutput
  (allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection)
  (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) Ncrt)
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I)
  U basis R S.value gridVolume τ : ℝ) : ℂ)
local notation "actualTarget" => forecastLawDensityPhysicalTarget B U basis S actualLaw
  actualDensity selected sample xref actualActive actualOutput Ncrt gridVolume
  base box τ o hb bW

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
variable (radius : ℝ≥0) (hradius0 : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
variable (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
variable (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
  chartCap j * ‖v‖)
variable (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
  (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ box i ≤ box i)
variable (htrimbase : base ∈ trimmedIntegerBox box (spatialTrimMargin τ box))
variable (hVpos : 0 < gridVolume)
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((forecastGeometricJacobian (X := X) (I := I) U basis R S.value gridVolume τ : ℝ) : ℂ) * (forecastLawDensityPhysicalTarget B U basis S (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP) (allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c) (allocatedShortIntegerSelection U basis S.value) sample xref (fun _ : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => crtPolynomialInputLaw primes exponent (fun l => padicValNat (primes l) stepG) hcoprime (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l)))) (fun v : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => integerLongPolynomialOutput (allocatedForecastPolynomial (allocatedShortAxis (I := I) U basis S.value) base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) (∏ l, primes l ^ exponent l)) (∏ l, primes l ^ exponent l) gridVolume base box τ o hb bW) poly hpoly u - ∑ i, nativeCoeff i * (F i).eval box poly u‖ ≤ δnative)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hX : (Fintype.card X : ℝ) ≤ Pambient)
variable (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hlarge : ∀ i, Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (box i : ℝ))
variable (hRrank : Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ))
  Rrank (U j) (nativePoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
variable (hPdecay : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) + 2 : ℕ) : ℝ) ≤ Pdecay)
variable (hdecay : ∀ i (χ : AddChar ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod (∏ l, primes l ^ exponent l)) ℂ),
  ‖finiteImageCharacteristic ((fun _ : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => crtPolynomialInputLaw primes exponent (fun l => padicValNat (primes l) stepG) hcoprime (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l)))) i) (fun x j => ((fun v : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => integerLongPolynomialOutput (allocatedForecastPolynomial (allocatedShortAxis (I := I) U basis S.value) base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) (∏ l, primes l ^ exponent l)) i x j : ZMod (∏ l, primes l ^ exponent l))) χ‖ ≤
    D * (orderOf χ : ℝ) ^ (-Pdecay))
variable (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U basis R S.value box τ j ≤ δgrid)

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hp hV hτ hξ hbox hframe hmem hdegree hbase hsmallChart hread
  hm hperiod hcover hqN ν hlattice hcompact hσ1 hradius0 hradius3 hradius hchartCap hchart hchartBudget
  hmargin htrimbase hVpos happrox hPambient hEprec hX hdim hLip hcoverF hmodF hmass
  hlarge hRrank hrank hcutoff hD hPdecay hdecay hδgrid hδgrid1 hgridmesh in

theorem allocatedFixedPath_sliced_native_ambient_comparison :
    ‖allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
        HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset -
      (𝔼 u ∈ integerBox box, W.eval box nativePoly u *
        (κ * actualTarget nativePoly hmem u))‖ ≤
      comparisonError + ((2 * δnative + M * Real.exp (-Eprec)) +
        allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := basis) (S := S)
          (E := E) (τ := τ) (ξ := ξ) (box := box) (integerFrame := integerFrame)
          (HG := HG) (hHG := hHG) (cG := cG) (stepG := stepG) (hstepG := hstepG)
          (e := e) (h0 := h0) (h1 := h1) (hδ := hδ) (o := o) (Lip := Lip)
          (cutoff := cutoff) (D := D) (δgrid := δgrid)) := by
  have hsource := allocatedFixedPath_sliced_recovered_native_rational_comparison
    B U basis hR hσ S primes exponent HP stepP cP hinsideP hHP τ ξ hτ hξ box hbox
    integerFrame hframe HG hHG cG stepG hstepG hcontainedG e h0 h1 hB sample hs ht
    hσbound H c hH hδ hsubset hdense q hsizeG hsmallG hsize hsmall hε hmesh hδone
    b hη A hA htail hb o bW W hm hperiod hcover xref base read hp hcoprime hqN hV
    nativePoly hmem hdegree hbase hsmallChart hread
  have hamb := allocatedFixedPath_sliced_ambient_rational_comparison
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ)
    (S := S) (primes := primes) (exponent := exponent) (HP := HP) (stepP := stepP)
    (cP := cP) (hinsideP := hinsideP) (hHP := hHP) (τ := τ) (ξ := ξ)
    (hτ := hτ) (hξ := hξ) (box := box) (hbox := hbox) (integerFrame := integerFrame)
    (hframe := hframe) (HG := HG) (hHG := hHG) (cG := cG) (stepG := stepG)
    (hstepG := hstepG) (hcontainedG := hcontainedG) (e := e) (h0 := h0) (h1 := h1)
    (hB := hB) (sample := sample) (hs := hs) (H := H) (c := c)
    (hH := hH) (hδ := hδ) (hsubset := hsubset) (hdense := hdense) (q := q)
    (hb := hb) (o := o) (bW := bW) (W := W) (hm := hm)
    (hperiod := hperiod) (hcover := hcover) (xref := xref) (base := base) (read := read)
    (hcoprime := hcoprime) (hqN := hqN) (nativePoly := nativePoly) (hmem := hmem) (hdegree := hdegree)
    (ν := ν) (hσ1 := hσ1) (radius := radius) (hradius0 := hradius0) (hradius3 := hradius3)
    (hradius := hradius) (chartCap := chartCap) (hchartCap := hchartCap) (hchart := hchart) (hchartBudget := hchartBudget)
    (hmargin := hmargin) (htrimbase := htrimbase) (hVpos := hVpos) (F := F) (nativeCoeff := nativeCoeff)
    (δnative := δnative) (happrox := happrox) (hPambient := hPambient) (hEprec := hEprec) (hX := hX)
    (hdim := hdim) (hLip := hLip) (hcoverF := hcoverF) (hmodF := hmodF) (hmass := hmass)
    (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank) (cutoff := cutoff) (hcutoff := hcutoff)
    (hD := hD) (hPdecay := hPdecay) (hdecay := hdecay) (hδgrid := hδgrid) (hδgrid1 := hδgrid1)
    (hgridmesh := hgridmesh)
  rw [norm_sub_rev] at hamb
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hsource hamb)

end Erdos3.VectorPolynomial

end

end OAI
