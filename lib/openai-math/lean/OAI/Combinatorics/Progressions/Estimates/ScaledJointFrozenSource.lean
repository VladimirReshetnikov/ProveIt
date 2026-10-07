/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import Mathlib.MeasureTheory.Measure.Prod
import OAI.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
import OAI.Combinatorics.Progressions.Sampling.CanonicalRawSampler

namespace OAI

section

namespace Erdos3

open MeasureTheory

def jointCubeScale {D α : Type*} {B : D → Type*} (h : D → ℕ)
    (T : PrincipalTupleIndex B h → ℝ) (x : JointBlockParameter B h α → ℝ)
    (j : JointBlockParameter B h α) : ℝ :=
  T ⟨j.1, j.2.1, j.2.2.1⟩ * x j

theorem jointCubeScale_measurable {D α : Type*} {B : D → Type*} (h : D → ℕ)
    (T : PrincipalTupleIndex B h → ℝ) : Measurable (jointCubeScale (α := α) h T) :=
  Measurable.of_eval (fun coordinate => measurable_const.mul (measurable_pi_apply coordinate))

noncomputable def jointCubeScaleHomeomorph {D α : Type*} {B : D → Type*} (h : D → ℕ)
    (T : PrincipalTupleIndex B h → ℝ) (hT : ∀ i, T i ≠ 0) :
    (JointBlockParameter B h α → ℝ) ≃ₜ (JointBlockParameter B h α → ℝ) :=
  Homeomorph.piCongrRight (fun j =>
    Homeomorph.smulOfNeZero (α := ℝ) (T ⟨j.1, j.2.1, j.2.2.1⟩) (hT _))

theorem jointCubeScaleHomeomorph_apply {D α : Type*} {B : D → Type*} (h : D → ℕ)
    (T : PrincipalTupleIndex B h → ℝ) (hT : ∀ i, T i ≠ 0)
    (x : JointBlockParameter B h α → ℝ) :
    jointCubeScaleHomeomorph h T hT x = jointCubeScale h T x := rfl

noncomputable def scaledJointCubeSource {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (T : PrincipalTupleIndex B h → ℝ) : Measure (JointBlockParameter B h α → ℝ) :=
  sigmaAxisMeasure (fun d => scaledBlockCubeMeasure (fun i : B d × Fin (h d) => T ⟨d, i⟩))

theorem scaledJointCubeSource_eq_map {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (T : PrincipalTupleIndex B h → ℝ) (hT : ∀ i, 0 < T i) :
    scaledJointCubeSource (α := α) h T =
      (jointBooleanSource h).map (jointCubeScale h T) := by
  change _ = (jointBooleanSource h).map
    (sigmaAxisSampler (fun d => blockCubeScale (α := α) (fun i : B d × Fin (h d) => T ⟨d, i⟩)))
  rw [jointBooleanSource, sigmaAxisSampler_image_law _ _
    (fun d => blockCubeScale_measurable (fun i : B d × Fin (h d) => T ⟨d, i⟩))]
  unfold scaledJointCubeSource
  congr 1
  funext d
  exact scaledBlockCubeMeasure_eq_map _ (fun i => hT ⟨d, i⟩)

theorem scaledJointCubeSource_probability {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (T : PrincipalTupleIndex B h → ℝ) (hT : ∀ i, 0 < T i) :
    IsProbabilityMeasure (scaledJointCubeSource (α := α) h T) := by
  rw [scaledJointCubeSource_eq_map h T hT]
  infer_instance

theorem scaledJointCubeSource_integral {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (T : PrincipalTupleIndex B h → ℝ) (hT : ∀ i, 0 < T i)
    (f : (JointBlockParameter B h α → ℝ) → ℝ) :
    (∫ x, f x ∂scaledJointCubeSource h T) =
      ∫ x, f (jointCubeScale h T x) ∂jointBooleanSource h := by
  rw [scaledJointCubeSource_eq_map h T hT]
  exact (jointCubeScaleHomeomorph h T (fun i => (hT i).ne')).toMeasurableEquiv.measurableEmbedding.integral_map f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def rawCanonicalCubeTuple {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B : D → Type*} {h : D → ℕ} (extra : G → Option α → Z)
    (scale : SamplerTupleIndex G B h → ℝ) (z : Z → ℝ)
    (x : JointBlockParameter B h α → ℝ) (vertex : Finset α) : SamplerTupleIndex G B h → ℝ
  | .inl g => scale (.inl g) * ∑ r : Option α, (booleanFeature r vertex : ℝ) * z (extra g r)
  | .inr ⟨d, b, v⟩ => scalarCubeValue (fun r => x ⟨d, b, v, r⟩) vertex

theorem rawCanonicalCubeTuple_rescale {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B : D → Type*} {h : D → ℕ} (extra : G → Option α → Z)
    (scale : SamplerTupleIndex G B h → ℝ) (z : Z → ℝ)
    (x : JointBlockParameter B h α → ℝ) (vertex : Finset α) (k : SamplerTupleIndex G B h) :
    rawCanonicalCubeTuple extra scale z (jointCubeScale h (fun i => scale (.inr i)) x) vertex k =
      scale k * normalizedCubeTuple (canonicalTupleInput extra) z x vertex k := by
  cases k with
  | inl g => rfl
  | inr i =>
    rcases i with ⟨d, b, v⟩
    exact scalarCubeValue_smul (scale (.inr ⟨d, b, v⟩)) (fun r => x ⟨d, b, v, r⟩) vertex

noncomputable def rawCanonicalJet {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : D → ℝ)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) : (Σ d, O d) → ℝ :=
  rawProductArrayJet h sets terms exponent (fun d b v => .inr ⟨d, b, v⟩)
    (scaledPrincipalCoefficient h Q scale (fun d b v => .inr ⟨d, b, v⟩) c)
    (scaledTailCoefficient Q scale weight exponent coefficientIndex t z)
    (fun d => Q d * constant d) Q (rawCanonicalCubeTuple extra scale z x)

theorem rawCanonicalJet_rescale {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : D → ℝ)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) :
    rawCanonicalJet h c sets terms weight exponent coefficientIndex extra Q scale constant t z
      (jointCubeScale h (fun i => scale (.inr i)) x) =
      canonicalScaledProductArrayJet h c sets terms weight exponent coefficientIndex extra
        Q scale constant t z x := by
  unfold rawCanonicalJet canonicalScaledProductArrayJet scaledProductArrayJet
  have he : rawCanonicalCubeTuple extra scale z (jointCubeScale h (fun i => scale (.inr i)) x) =
      fun vertex k => scale k * normalizedCubeTuple (canonicalTupleInput extra) z x vertex k := by
    funext vertex k
    exact rawCanonicalCubeTuple_rescale extra scale z x vertex k
  rw [he]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem scaledJointCubeSource_prod {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype α] [DecidableEq α] {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (T : PrincipalTupleIndex B h → ℝ) (hT : ∀ i, 0 < T i)
    (μ : Measure Ω) [SFinite μ] :
    μ.prod (scaledJointCubeSource (α := α) h T) =
      (μ.prod (jointBooleanSource h)).map (Prod.map id (jointCubeScale h T)) := by
  rw [scaledJointCubeSource_eq_map h T hT]
  simpa only [Measure.map_id] using
    Measure.map_prod_map μ (jointBooleanSource h) measurable_id (jointCubeScale_measurable h T)

theorem scaledJointCubeSource_prod_integral {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype α] [DecidableEq α] {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (T : PrincipalTupleIndex B h → ℝ) (hT : ∀ i, 0 < T i)
    (μ : Measure Ω) [SFinite μ] (f : Ω × (JointBlockParameter B h α → ℝ) → ℝ) :
    (∫ p, f p ∂μ.prod (scaledJointCubeSource h T)) =
      ∫ p, f (p.1, jointCubeScale h T p.2) ∂μ.prod (jointBooleanSource h) := by
  rw [scaledJointCubeSource_prod h T hT]
  exact ((MeasurableEquiv.refl Ω).prodCongr
    (jointCubeScaleHomeomorph h T (fun i => (hT i).ne')).toMeasurableEquiv).measurableEmbedding.integral_map f

end Erdos3

end

end OAI
