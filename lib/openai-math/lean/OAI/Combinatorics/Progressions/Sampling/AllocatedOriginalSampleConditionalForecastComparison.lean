import OAI.Combinatorics.Progressions.Lattices.AllocatedActiveResidueComparison
import OAI.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleFullResidueRiemann

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

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

theorem allocatedOriginalSample_conditional_forecast_comparison
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
    (q : ℕ) (hq : 0 < q) (residue : FullInput → Option Empty → ZMod q)
    (hcell : 0 < (principalTupleWeights (α := Empty) B degree sides hSides).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = residue)))
    (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : ShortTuple → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ u, LipschitzWith Kφ (φ u)) (hφone : ∀ u y, ‖φ u y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    ‖(∫ z, ((principalTupleWeights (α := Empty) B degree sides hSides).condition
        (Finset.univ.filter (fun y => principalResidueLabel q y = residue)) hcell).complexMean
        (fun v => φ (principalAxisRestrict short v)
          (z, allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
            sample (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value)))
          ∂canonicalZeroSpatialLaw (X := X) s root D W L) -
      (allocatedShortPrincipalResidueLaw B U basis S q residue hcell).complexMean
        (fun u => ∫ y, φ u y ∂realDensityMeasure volume (allocatedOriginalSampleForecastDensity (X := X)
          B U basis S s root D hp hW hL hB lower width sample))‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) := by
  classical
  intro lower width K
  let μ := canonicalZeroSpatialLaw (X := X) s root D W L
  let := canonicalZeroSpatialLaw_probability (X := X) s root D hp hW hL
  let pA := principalResidueWeights activeB activeDegree (fun _ => S.value)
    (fun _ => S.positive) q hq (fun j => residue ⟨j.1.val, j.2⟩)
    (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)
  let pShort := allocatedShortPrincipalResidueLaw B U basis S q residue hcell
  let F := allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1) sample
  let f := fun (z : (Σ _ : X, Unit ⊕ Empty) → ℝ) (u : ShortTuple)
    (v : PrincipalIntegerTuples activeB activeDegree Empty (fun _ => S.value)) =>
      φ u (z, F (fun j => (v j none : ℝ) / S.value))
  have hint (u : ShortTuple) : Integrable (fun z => pA.complexMean (f z u)) μ := by
    apply pA.complexMean_integrable
    intro v
    have hm : Measurable (fun z => f z u v) :=
      (hφ u).continuous.measurable.comp (measurable_id.prodMk measurable_const)
    exact ⟨hm.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun z => hφone u _))⟩
  have hpart (z : (Σ _ : X, Unit ⊕ Empty) → ℝ) :=
    allocatedPrincipalResidue_integer_partition B U basis S q residue hcell hq hsize
      (fun u v => φ u (z, F (fun j => (v j : ℝ) / S.value)))
  have heq : (∫ z, ((principalTupleWeights (α := Empty) B degree sides hSides).condition
        (Finset.univ.filter (fun y => principalResidueLabel q y = residue)) hcell).complexMean
        (fun v => φ (principalAxisRestrict short v)
          (z, F (fun j => (((principalAxisRestrict (fun a => ¬short a) v) j none : ℤ) : ℝ) / S.value))) ∂μ) =
      pShort.complexMean (fun u => ∫ z, pA.complexMean (f z u) ∂μ) := by
    calc
      _ = ∫ z, pShort.complexMean (fun u => pA.complexMean (f z u)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpart)
      _ = _ := pShort.integral_complexMean μ _ hint
  rw [heq]
  apply (pShort.norm_complexMean_sub_le _ _ (fun _ =>
    2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
      ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value))) ?_).trans_eq
    (pShort.mean_const _)
  intro u _
  exact allocatedOriginalSampleForecastDensity_full_residue_complex_riemann
    B U basis hR hσ S s root D hp hW hL hB hroot sample hs hS q hq
    (fun j => residue ⟨j.1.val, j.2⟩) hsize hsmall (φ u) (hφ u) (hφone u)

end Erdos3.VectorPolynomial

end

end OAI
