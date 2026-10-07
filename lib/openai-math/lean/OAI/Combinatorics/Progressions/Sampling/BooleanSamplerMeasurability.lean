/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.CoefficientTailScaling

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem jointBooleanSampler_formula {D α : Type*} [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) :
    jointBooleanSampler h c sets x o = booleanCoefficient
      (fun t => ∑ b : B o.1, c o.1 b * ∏ v : Fin (h o.1),
        ∑ r : Option α, (booleanFeature r t : ℝ) * x ⟨o.1, (b, v, r)⟩) (sets o.1 o.2) := by
  apply booleanSamplerMap_formula

theorem jointBooleanSampler_measurable_comp {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {B O : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun ω => c ω d b))
    (x : Ω → JointBlockParameter B h α → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) :
    Measurable (fun ω => jointBooleanSampler h (c ω) sets (x ω)) := by
  apply Measurable.of_eval
  intro o
  simp_rw [jointBooleanSampler_formula, booleanCoefficient]
  fun_prop

theorem normalizedCoefficientTailValue_measurable_comp {Ω T K Z I α : Type*}
    [MeasurableSpace Ω] [Fintype Z] [Fintype I] [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I) (s : Finset α)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → I → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) :
    Measurable (fun ω => normalizedCoefficientTailValue terms weight exponent coefficientIndex inputIndex
      (z ω) (x ω) s) := by
  have he : (fun ω => normalizedCoefficientTailValue terms weight exponent coefficientIndex inputIndex
      (z ω) (x ω) s) = fun ω => MvPolynomial.eval (polynomialParameterPoint 0 (z ω) (x ω))
        (normalizedCoefficientTail terms weight exponent coefficientIndex inputIndex s) :=
    funext (fun ω => (normalizedCoefficientTail_eval _ _ _ _ _ 0 _ _ _).symm)
  rw [he]
  apply (mvPolynomial_contDiff_eval _).continuous.measurable.comp
  apply Measurable.of_eval
  intro j
  rcases j with _ | (j | i)
  · exact measurable_const
  · exact hz j
  · exact hx i

theorem coefficientArraySampler_measurable_comp {Ω D K Z α : Type*}
    [MeasurableSpace Ω] [Fintype D] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O T : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) (t : ℝ)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun ω => c ω d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → JointBlockParameter B h α → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) :
    Measurable (fun ω => coefficientArraySampler h (c ω) sets terms weight exponent
      coefficientIndex inputIndex t (z ω) (x ω)) := by
  apply Measurable.of_eval
  intro o
  exact ((measurable_pi_apply o).comp (jointBooleanSampler_measurable_comp h sets c hc x hx)).add
    (measurable_const.mul (normalizedCoefficientTailValue_measurable_comp (terms o.1) (weight o.1)
      (exponent o.1) (coefficientIndex o.1) inputIndex (sets o.1 o.2) z hz x hx))

theorem jointBooleanSampler_measurable_frozen {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {B O : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b)) :
    Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      jointBooleanSampler h (c p.1) sets p.2) :=
  jointBooleanSampler_measurable_comp (Ω := Ω × (JointBlockParameter B h α → ℝ)) h sets
    (fun p => c p.1) (fun d b => (hc d b).comp measurable_fst)
    (fun p => p.2) (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem coefficientArraySampler_measurable_frozen {Ω D K Z α : Type*}
    [MeasurableSpace Ω] [Fintype D] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O T : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) (t : ℝ)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j)) :
    Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      coefficientArraySampler h (c p.1) sets terms weight exponent coefficientIndex inputIndex t
        (z p.1) p.2) :=
  coefficientArraySampler_measurable_comp (Ω := Ω × (JointBlockParameter B h α → ℝ))
    h sets terms weight exponent coefficientIndex inputIndex t
    (fun p => c p.1) (fun d b => (hc d b).comp measurable_fst)
    (fun p => z p.1) (fun j => (hz j).comp measurable_fst)
    (fun p => p.2) (fun i => (measurable_pi_apply i).comp measurable_snd)

end Erdos3

end

end OAI
