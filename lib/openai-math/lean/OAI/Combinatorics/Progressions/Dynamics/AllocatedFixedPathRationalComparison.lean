import OAI.Combinatorics.Progressions.Estimates.AllocatedJointRationalReference
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
import OAI.Combinatorics.Progressions.Lattices.AllocatedFixedPathSlicedKernelResidueRiemann

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Active" => PrincipalTupleIndex
  (fun a : {a // ¬short a} => B (Subtype.val a))
  (fun a : {a // ¬short a} => layerSamplerDegree I n (Subtype.val a))
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "law" => principalTupleWeights (α := Empty) B degree sides hSides

variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance fixedPathCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩

theorem allocatedFixedPath_crtRationalForecast_reference
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (hp : ∀ l, (primes l).Prime) (hinj : Function.Injective primes)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    (origin : ∀ l, Long → ZMod (primes l ^ exponent l))
    {q : ℕ} [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Active → ZMod q)).complexMean (fun ar =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          test (forecastInactiveShortGrid B U basis S selected c u)
            (allocatedJointResidueOutput B U basis S base noise deck projection q rG
              (allocatedPrincipalResidueJoin B U basis S q u ar))))) =
      ∑' z, 𝔼 b : Out → ZMod N,
        ((rationalInactiveForecast (law)
          (fun _ => crtPolynomialInputLaw primes exponent (fun _ => 0) hcoprime origin)
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            test z (fun j => ZMod.castHom hq (ZMod q) (b j)) := by
  simpa only [allocatedJointResidueOutput_join, FiniteProbabilityWeights.complexMean_const] using
    (allocatedJoint_crtRationalForecast_reference B U basis S primes exponent hR hσ
      selected hsmall c hc base noise deck projection hp hinj hcoprime origin hq hV
      (FiniteProbabilityWeights.uniform Unit) (fun _ => xref) (fun _ => test))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
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

include hR hσ in
theorem allocatedFixedPath_full_principal_residue_riemann
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (b : ∀ a : Active, B a.val) {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (hS : 2 ≤ S.value) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (G → ZMod q) → (FullInput → Option Empty → ZMod q) → ShortTuple → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ rG r u, LipschitzWith Kφ (φ rG r u))
    (hbound : ∀ rG r u y, ‖φ rG r u y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
        φ (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v) (principalAxisRestrict short v)
          (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short v) (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)))) -
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ k, ∫ v, φ rG (allocatedPrincipalResidueJoin B U basis S q u rA) u (fixedSpatialKernelMap budget (S.value : ℝ) z k,
            allocatedOriginalSampleLiftMap B U basis S lower width sample v)
            ∂unitBoxMeasure Input ∂unitBoxMeasure G)))‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) := by
  classical
  intro lower width K kernel law
  let shortLaw := allocatedUnconditionalShortPrincipalLaw B U basis S
  let active := FiniteProbabilityWeights.pi (fun _ : Input => integerScalarCubeWeights Empty S.value S.positive)
  let E := ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
      (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
    (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
      (Fintype.card G * ((q : ℝ) / S.value))
  let value := fun (x : G → IntegerScalarCubeBox Empty S.value) (u : ShortTuple) (v : Input → ℤ) =>
    φ (fun g => ((x g none : ℤ) : ZMod q))
      (allocatedPrincipalResidueJoin B U basis S q u (fun j => (v j : ZMod q))) u
      (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value),
        allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j : ℝ) / S.value))
  have hlabel (v : Original) :
      allocatedPrincipalResidueJoin B U basis S q (principalAxisRestrict short v)
        (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ZMod q)) =
        principalResidueLabel q v := by
    rw [← allocatedPrincipalResidueJoin_label_join B U basis S q,
      principalAxisJoin_restrict]
  have hpart (x : G → IntegerScalarCubeBox Empty S.value) :=
    allocatedPrincipal_integer_partition B U basis S (value x)
  simp only [value, hlabel] at hpart
  dsimp only [law]
  simp_rw [hpart]
  rw [FiniteProbabilityWeights.complexMean_commute kernel shortLaw]
  apply (shortLaw.norm_complexMean_sub_le _ _ (fun _ => E) ?_).trans_eq (shortLaw.mean_const E)
  intro u _
  exact allocatedFixedPath_joint_residue_riemann B U basis hR hσ S z hz u sample hs
    ht hσbound b hη A hA htail hS q hsize hsmall
    (fun rG rA => φ rG (allocatedPrincipalResidueJoin B U basis S q u rA) u)
    (fun rG rA => hφ rG _ u) (fun rG rA => hbound rG _ u)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance fixedPathComparisonCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

include hR hσ in
theorem allocatedFixedPath_rational_forecast_comparison
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (b : ∀ a : Active, B a.val) {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (hS : 2 ≤ S.value) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    {Cidx : Type*} (selected : Cidx → Σ j : Fin m, Fin (n j))
    (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (physicalNoise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (hp : ∀ l, (primes l).Prime) (hinj : Function.Injective primes)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    (origin : ∀ l, Long → ZMod (primes l ^ exponent l))
    (hqN : q ∣ N) {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ grid residue, LipschitzWith Kφ (test grid residue))
    (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1) :
    let c := fun a => (sample (selected a).1).2 (selected a).2
    let poly := allocatedForecastPolynomial short base physicalNoise deck projection
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let law := principalTupleWeights (α := Empty) B degree sides hSides
    ‖kernel.complexMean (fun x => law.complexMean (fun v =>
        test (forecastInactiveShortGrid B U basis S selected c (principalAxisRestrict short v))
          (allocatedJointResidueOutput B U basis S base physicalNoise deck projection q
            (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v))
          (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short v)
              (fun _ _ => 0) (fun _ _ => 1) sample
              (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)))) -
      (∑' grid, 𝔼 residue : Out → ZMod N,
        ((rationalInactiveForecast law
          (fun _ => crtPolynomialInputLaw primes exponent (fun _ => 0) hcoprime origin)
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume grid residue / gridVolume : ℝ) : ℂ) *
          ∫ k, ∫ v, test grid (fun j => ZMod.castHom hqN (ZMod q) (residue j))
            (fixedSpatialKernelMap budget (S.value : ℝ) z k,
              allocatedOriginalSampleLiftMap B U basis S lower width sample v)
            ∂unitBoxMeasure Input ∂unitBoxMeasure G)‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) := by
  classical
  intro c poly lower width K kernel law
  have hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support := by
    intro a d
    exact ((mixedArraySupported_iff_rows _ _ _ (sample (selected a).1)).mp
      (hs (selected a).1)).2 (selected a).2 d
  have he := allocatedFixedPath_full_principal_residue_riemann B U basis hR hσ S
    z hz sample hs ht hσbound b hη A hA htail hS q hsize hsmall
    (fun rG r u => test (forecastInactiveShortGrid B U basis S selected c u)
      (allocatedJointResidueOutput B U basis S base physicalNoise deck projection q rG r))
    (fun _ _ _ => hφ _ _) (fun _ _ _ => hbound _ _)
  have href := allocatedFixedPath_crtRationalForecast_reference B U basis S primes exponent
    hR hσ selected hshort c hc xref base physicalNoise deck projection hp hinj hcoprime origin hqN hV
    (fun grid residue => ∫ k, ∫ v, test grid residue
      (fixedSpatialKernelMap budget (S.value : ℝ) z k,
        allocatedOriginalSampleLiftMap B U basis S lower width sample v)
      ∂unitBoxMeasure Input ∂unitBoxMeasure G)
  dsimp only [lower, width] at he href
  rw [href] at he
  exact he

end Erdos3.VectorPolynomial

end

end OAI
