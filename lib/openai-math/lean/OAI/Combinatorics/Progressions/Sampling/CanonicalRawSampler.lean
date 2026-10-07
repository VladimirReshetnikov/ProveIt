import OAI.Combinatorics.Progressions.Estimates.RawProductArrayNormalization

namespace OAI

section

namespace Erdos3

noncomputable def canonicalScaledProductArrayJet {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : D → ℝ)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) : (Σ d, O d) → ℝ :=
  scaledProductArrayJet h c sets terms weight exponent (fun d j v => .inr ⟨d, j, v⟩)
    coefficientIndex (canonicalTupleInput extra) Q scale constant t z x

theorem canonicalScaledProductArrayJet_eq {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : D → ℝ)
    (hQ : ∀ d, Q d ≠ 0) (hscale : ∀ k, scale k ≠ 0)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) :
    canonicalScaledProductArrayJet h c sets terms weight exponent coefficientIndex extra Q scale constant t z x =
      booleanConstantJet sets constant + coefficientArraySampler h c sets terms weight exponent
        coefficientIndex (canonicalTupleInput extra) t z x :=
  scaledProductArrayJet_eq h c sets terms weight exponent _ coefficientIndex (canonicalTupleInput extra)
    (fun _ _ _ _ => rfl) Q scale constant hQ hscale t z x

theorem canonicalScaledProductArrayJet_zero {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : D → ℝ)
    (hQ : ∀ d, Q d ≠ 0) (hscale : ∀ k, scale k ≠ 0)
    (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) :
    canonicalScaledProductArrayJet h c sets terms weight exponent coefficientIndex extra Q scale constant 0 z x =
      booleanConstantJet sets constant + jointBooleanSampler h c sets x := by
  rw [canonicalScaledProductArrayJet_eq h c sets terms weight exponent coefficientIndex extra Q scale constant hQ hscale,
    coefficientArraySampler_zero]

end Erdos3

end

end OAI
