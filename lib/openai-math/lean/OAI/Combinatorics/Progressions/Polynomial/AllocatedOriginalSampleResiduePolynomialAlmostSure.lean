import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastDensityRiemann

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option Empty → ZMod q)
variable (hsize : ∀ j, (Fintype.card Empty + 1) * q ≤ H j)

local notation "law" => containedProgressionResidueLaw B h L H step c hL hH hsubset q hq r hsize

theorem containedProgressionResidueLaw_polynomial
    (poly : MvPolynomial (PrincipalTupleIndex B h) ℤ)
    (v : PrincipalIntegerTuples B h Empty L) (hv : (law).weight v ≠ 0) :
    ((MvPolynomial.eval (fun j => (v j none : ℤ)) poly : ℤ) : ZMod q) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (fun j => (c j : ZMod q) + (step j : ZMod q) * r j none) poly := by
  rw [integerPolynomial_eval_residue]
  congr 1
  funext j
  change ((v j none : ℤ) : ZMod q) = _
  simpa only [ite_true] using
    containedProgressionResidueLaw_support B h L H step c hL hH hsubset q hq r hsize v hv j none

theorem containedProgressionResidueLaw_polynomial_test
    {Out : Type*} (poly : Out → MvPolynomial (PrincipalTupleIndex B h) ℤ)
    (f : (Out → ZMod q) → PrincipalIntegerTuples B h Empty L → ℂ) :
    (law).complexMean (fun v => f (fun o => ((MvPolynomial.eval (fun j => (v j none : ℤ)) (poly o) : ℤ) : ZMod q)) v) =
      (law).complexMean (fun v => f (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (fun j => (c j : ZMod q) + (step j : ZMod q) * r j none) (poly o)) v) := by
  unfold FiniteProbabilityWeights.complexMean
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : (law).weight v = 0
  · simp only [hv, Complex.ofReal_zero, zero_mul]
  · have he (o : Out) := containedProgressionResidueLaw_polynomial
      B h L H step c hL hH hsubset q hq r hsize (poly o) v hv
    simp only [he]

end Erdos3

end

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

theorem allocatedOriginalSampleForecastDensity_polynomial_residue_riemann
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    {Out : Type*} (poly : Out → MvPolynomial Input ℤ)
    (φ : (Out → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ)) → ℂ)
    {Kφ : ℝ≥0} (hφ : ∀ r, LipschitzWith Kφ (φ r))
    (hφone : ∀ r y, ‖φ r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    let outres := fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (fun j => (c j : ZMod q) + (step j : ZMod q) * residue j none) (poly o)
    ‖(∫ z, (containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
        (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)).complexMean
        (fun v => φ (fun o => ((MvPolynomial.eval (fun j => (v j none : ℤ)) (poly o) : ℤ) : ZMod q)) (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∫ y, φ outres y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
        B U basis S s root D hp hW hL hB lower width sample)‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε) := by
  classical
  intro lower width K outres
  have he (z : (Σ _ : X, Unit ⊕ Empty) → ℝ) :=
    containedProgressionResidueLaw_polynomial_test activeB activeDegree (fun _ => S.value)
      H step c (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
      (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)
      poly (fun r v => φ r (z, allocatedOriginalSampleLiftMap B U basis S
        (fun _ _ => 0) (fun _ _ => 1) sample (fun j => (v j none : ℝ) / S.value)))
  simp_rw [he]
  exact allocatedOriginalSampleForecastDensity_contained_residue_complex_riemann
    B U basis hR hσ S s root D hp hW hL hB hroot sample hs
    step H c hstep hH hδ hsubset hdense q hq residue hsize hsmall hε hmesh
    (φ outres) (hφ outres) (hφone outres)

end Erdos3.VectorPolynomial

end

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

theorem allocatedOriginalSampleForecastDensity_polynomial_residue_ae_riemann
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    {Out : Type*} (poly : Sample → Out → MvPolynomial Input ℤ)
    (φ : Sample → (Out → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ)) → ℂ)
    {Kφ : ℝ≥0} (hφ : ∀ sample r, LipschitzWith Kφ (φ sample r))
    (hφone : ∀ sample r y, ‖φ sample r y‖ ≤ 1) :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    let outres := fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (fun j => (c j : ZMod q) + (step j : ZMod q) * residue j none) (poly sample o)
    ‖(∫ z, (containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
        (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)).complexMean
        (fun v => φ sample (fun o => ((MvPolynomial.eval (fun j => (v j none : ℤ)) (poly sample o) : ℤ) : ZMod q)) (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      ∫ y, φ sample outres y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
        B U basis S s root D hp hW hL hB lower width sample)‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε) := by
  filter_upwards [allocatedCoefficientSource_supported B U basis hR hσ S] with sample hs
  exact allocatedOriginalSampleForecastDensity_polynomial_residue_riemann
    B U basis hR hσ S s root D hp hW hL hB hroot sample hs
    step H c hstep hH hδ hsubset hdense q hq residue hsize hsmall hε hmesh
    (poly sample) (φ sample) (hφ sample) (hφone sample)

end Erdos3.VectorPolynomial

end

end OAI
