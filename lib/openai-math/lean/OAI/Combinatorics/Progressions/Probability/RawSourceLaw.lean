import OAI.Combinatorics.Progressions.Estimates.ConstantJetPostprocessing

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {Ω D G Z α : Type*} [Fintype α] [DecidableEq α]
  {B O L : D → Type*} [∀ d, Fintype (B d)]

noncomputable def canonicalRawOutput (h : D → ℕ) (c : Ω → ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : Ω → SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ)
    (t : ℝ) (z : Ω → Z → ℝ) (p : Ω × (JointBlockParameter B h α → ℝ)) : (Σ d, O d) → ℝ :=
  canonicalScaledProductArrayJet h (c p.1) sets terms weight exponent coefficientIndex extra
    (Q p.1) (scale p.1) (constant p.1) t (z p.1) p.2

theorem canonicalRawOutput_eq (h : D → ℕ) (c : Ω → ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : Ω → SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ)
    (hQ : ∀ a d, Q a d ≠ 0) (hscale : ∀ a k, scale a k ≠ 0) (t : ℝ) (z : Ω → Z → ℝ) :
    canonicalRawOutput h c sets terms weight exponent coefficientIndex extra Q scale constant t z =
      fun p => booleanConstantJet sets (constant p.1) + coefficientArraySampler h (c p.1) sets terms
        weight exponent coefficientIndex (canonicalTupleInput extra) t (z p.1) p.2 := by
  funext p
  exact canonicalScaledProductArrayJet_eq h (c p.1) sets terms weight exponent coefficientIndex extra
    (Q p.1) (scale p.1) (constant p.1) (hQ p.1) (hscale p.1) t (z p.1) p.2

theorem canonicalRawOutput_joint_map [MeasurableSpace Ω]
    (h : D → ℕ) (c : Ω → ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : Ω → SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ)
    (hQ : ∀ a d, Q a d ≠ 0) (hscale : ∀ a k, scale a k ≠ 0) (t : ℝ) (z : Ω → Z → ℝ)
    (μ : Measure (Ω × (JointBlockParameter B h α → ℝ))) :
    μ.map (fun p => (p.1, canonicalRawOutput h c sets terms weight exponent coefficientIndex extra
      Q scale constant t z p)) =
      μ.map (fun p => (p.1, booleanConstantJet sets (constant p.1) +
        coefficientArraySampler h (c p.1) sets terms weight exponent coefficientIndex
          (canonicalTupleInput extra) t (z p.1) p.2)) := by
  rw [canonicalRawOutput_eq h c sets terms weight exponent coefficientIndex extra Q scale constant hQ hscale]

theorem canonicalRawOutput_measurable [MeasurableSpace Ω] [Fintype D] [Fintype Z]
    (h : D → ℕ) (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : Ω → SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ)
    (hQ : ∀ a d, Q a d ≠ 0) (hscale : ∀ a k, scale a k ≠ 0)
    (hconstant : ∀ d, Measurable (fun a => constant a d))
    (t : ℝ) (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j)) :
    Measurable (canonicalRawOutput h c sets terms weight exponent coefficientIndex extra Q scale constant t z) := by
  rw [canonicalRawOutput_eq h c sets terms weight exponent coefficientIndex extra Q scale constant hQ hscale]
  exact ((booleanConstantJet_measurable_comp sets constant hconstant).comp measurable_fst).add
    (coefficientArraySampler_measurable_frozen h sets terms weight exponent coefficientIndex
      (canonicalTupleInput extra) t c hc z hz)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {Ω D G Z α : Type*} [Fintype α] [DecidableEq α]
  {B O L : D → Type*} [∀ d, Fintype (B d)]

noncomputable def rawSourceOutput (h : D → ℕ) (c : Ω → ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ)
    (t : ℝ) (z : Ω → Z → ℝ) (p : Ω × (JointBlockParameter B h α → ℝ)) : (Σ d, O d) → ℝ :=
  rawCanonicalJet h (c p.1) sets terms weight exponent coefficientIndex extra
    (Q p.1) scale (constant p.1) t (z p.1) p.2

theorem rawSourceOutput_rescale (h : D → ℕ) (c : Ω → ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ)
    (t : ℝ) (z : Ω → Z → ℝ) (p : Ω × (JointBlockParameter B h α → ℝ)) :
    rawSourceOutput h c sets terms weight exponent coefficientIndex extra Q scale constant t z
      (p.1, jointCubeScale h (fun i => scale (.inr i)) p.2) =
      canonicalRawOutput h c sets terms weight exponent coefficientIndex extra Q (fun _ => scale)
        constant t z p :=
  rawCanonicalJet_rescale h (c p.1) sets terms weight exponent coefficientIndex extra
    (Q p.1) scale (constant p.1) t (z p.1) p.2

theorem rawSourceOutput_measurable [MeasurableSpace Ω] [Fintype D] [Fintype Z]
    (h : D → ℕ) (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ)
    (hQ : ∀ a d, Q a d ≠ 0) (hscale : ∀ k, scale k ≠ 0)
    (hconstant : ∀ d, Measurable (fun a => constant a d))
    (t : ℝ) (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j)) :
    Measurable (rawSourceOutput h c sets terms weight exponent coefficientIndex extra Q scale constant t z) := by
  let e := jointCubeScaleHomeomorph (α := α) h (fun i => scale (.inr i)) (fun i => hscale (.inr i))
  have he : rawSourceOutput h c sets terms weight exponent coefficientIndex extra Q scale constant t z =
      canonicalRawOutput h c sets terms weight exponent coefficientIndex extra Q (fun _ => scale)
        constant t z ∘ Prod.map id e.symm := by
    funext p
    rcases p with ⟨a, x⟩
    have hx := rawSourceOutput_rescale h c sets terms weight exponent coefficientIndex extra
      Q scale constant t z (a, e.symm x)
    change rawSourceOutput h c sets terms weight exponent coefficientIndex extra Q scale constant t z
      (a, e (e.symm x)) = _ at hx
    simpa only [e.apply_symm_apply, Function.comp_apply, Prod.map_apply, id_eq] using hx
  rw [he]
  exact (canonicalRawOutput_measurable h c hc sets terms weight exponent coefficientIndex extra
    Q (fun _ => scale) constant hQ (fun _ k => hscale k) hconstant t z hz).comp
      (measurable_id.prodMap e.symm.continuous.measurable)

theorem rawSourceOutput_integral [MeasurableSpace Ω] [Fintype D]
    (h : D → ℕ) (c : Ω → ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ)
    (hscale : ∀ i, 0 < scale (.inr i)) (t : ℝ) (z : Ω → Z → ℝ)
    (μ : Measure Ω) [SFinite μ] (F : Ω × ((Σ d, O d) → ℝ) → ℝ) :
    (∫ p, F (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
      Q scale constant t z p) ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))) =
      ∫ p, F (p.1, canonicalRawOutput h c sets terms weight exponent coefficientIndex extra
        Q (fun _ => scale) constant t z p) ∂μ.prod (jointBooleanSource h) := by
  rw [scaledJointCubeSource_prod_integral h _ hscale]
  simp only [rawSourceOutput_rescale]

theorem rawSourceOutput_joint_law [MeasurableSpace Ω] [Fintype D] [Fintype Z]
    (h : D → ℕ) (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ)
    (hQ : ∀ a d, Q a d ≠ 0) (hscale : ∀ k, 0 < scale k)
    (hconstant : ∀ d, Measurable (fun a => constant a d))
    (t : ℝ) (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (μ : Measure Ω) [SFinite μ] :
    (μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))).map
      (fun p => (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
        Q scale constant t z p)) =
      (μ.prod (jointBooleanSource h)).map
        (fun p => (p.1, canonicalRawOutput h c sets terms weight exponent coefficientIndex extra
          Q (fun _ => scale) constant t z p)) := by
  have hr := rawSourceOutput_measurable h c hc sets terms weight exponent coefficientIndex extra
    Q scale constant hQ (fun k => (hscale k).ne') hconstant t z hz
  rw [scaledJointCubeSource_prod h _ (fun i => hscale (.inr i)),
    Measure.map_map (measurable_fst.prodMk hr)
      (measurable_id.prodMap (jointCubeScale_measurable h _))]
  congr 1
  funext p
  exact Prod.ext rfl (rawSourceOutput_rescale h c sets terms weight exponent coefficientIndex extra
    Q scale constant t z p)

end Erdos3

end

end OAI
