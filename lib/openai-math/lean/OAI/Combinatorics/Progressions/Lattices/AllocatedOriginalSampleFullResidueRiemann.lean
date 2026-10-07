import OAI.Combinatorics.Progressions.Polynomial.AllocatedOriginalSampleResiduePolynomialAlmostSure

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
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
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

theorem allocatedOriginalSampleForecastDensity_full_residue_riemann
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value)
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    {Out : Type*} (poly : Out → MvPolynomial Input ℤ)
    (φ : (Out → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ)) → ℂ)
    {Kφ : ℝ≥0} (hφ : ∀ r, LipschitzWith Kφ (φ r))
    (hφone : ∀ r y, ‖φ r y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    let outres := fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (fun j => residue j none) (poly o)
    ‖(∫ z, (principalResidueWeights activeB activeDegree (fun _ => S.value)
        (fun _ => S.positive) q hq residue
        (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)).complexMean
        (fun v => φ (fun o => ((MvPolynomial.eval (fun j => (v j none : ℤ)) (poly o) : ℤ) : ZMod q)) (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∫ y, φ outres y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
        B U basis S s root D hp hW hL hB lower width sample)‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) := by
  classical
  intro lower width K outres
  have he := allocatedOriginalSampleForecastDensity_polynomial_residue_riemann
    B U basis hR hσ S s root D hp hW hL hB hroot sample hs
    (fun _ => 1) (fun _ => S.value) (fun _ => 0)
    (fun _ => Nat.zero_lt_one) (fun _ => hS) (δ := 1) zero_lt_one
    (fun _ => fullIntervalProgression_subset S.value)
    (fun _ => by simp only [Nat.cast_one, fullIntervalProgression_card, one_mul, le_refl])
    q hq residue (fun _ => hsize) (fun _ => hsmall)
    (ε := 1 / S.value) (by positivity) (fun _ => by simp only [Nat.cast_one, le_refl])
    poly φ hφ hφone
  dsimp only at he
  rw [containedProgressionResidueLaw_fullInterval] at he
  simpa only [Int.cast_zero, Nat.cast_one, zero_add, one_mul, zero_div,
    lower, width, K, outres] using he

theorem allocatedOriginalSampleForecastDensity_full_residue_complex_riemann
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hS : 2 ≤ S.value)
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ)) → ℂ)
    {Kφ : ℝ≥0} (hφ : LipschitzWith Kφ φ)
    (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    ‖(∫ z, (principalResidueWeights activeB activeDegree (fun _ => S.value)
        (fun _ => S.positive) q hq residue
        (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)).complexMean
        (fun v => φ (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∫ y, φ y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
        B U basis S s root D hp hW hL hB lower width sample)‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) := by
  exact allocatedOriginalSampleForecastDensity_full_residue_riemann
    B U basis hR hσ S s root D hp hW hL hB hroot sample hs hS q hq residue hsize hsmall
    (fun e : Empty => e.elim) (fun _ => φ) (fun _ => hφ) (fun _ => hφone)

end Erdos3.VectorPolynomial

end

end OAI
