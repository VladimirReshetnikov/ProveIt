import OAI.Combinatorics.Progressions.Sampling.BooleanSamplerMeasurability

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D K Z α : Type*} [Fintype α] [DecidableEq α]
  {B O L : D → Type*} [∀ d, Fintype (B d)]

noncomputable def rawProductArrayValue (h : D → ℕ) (terms : ∀ d, Finset (L d))
    (exponent : ∀ d, L d → K →₀ ℕ) (principal : ∀ d, B d → Fin (h d) → K)
    (a : ∀ d, B d → ℝ) (b : ∀ d, L d → ℝ) (constant : D → ℝ) (y : K → ℝ) (d : D) : ℝ :=
  constant d + (∑ j, a d j * ∏ v, y (principal d j v)) +
    ∑ n ∈ terms d, b d n * ∏ k ∈ (exponent d n).support, y k ^ exponent d n k

noncomputable def rawProductArrayJet (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (L d)) (exponent : ∀ d, L d → K →₀ ℕ)
    (principal : ∀ d, B d → Fin (h d) → K)
    (a : ∀ d, B d → ℝ) (b : ∀ d, L d → ℝ) (constant Q : D → ℝ)
    (tuple : Finset α → K → ℝ) (o : Σ d, O d) : ℝ :=
  booleanCoefficient (fun vertex => rawProductArrayValue h terms exponent principal a b constant
    (tuple vertex) o.1) (sets o.1 o.2) / Q o.1

noncomputable def scaledPrincipalCoefficient (h : D → ℕ) (Q : D → ℝ) (scale : K → ℝ)
    (principal : ∀ d, B d → Fin (h d) → K) (c : ∀ d, B d → ℝ) (d : D) (j : B d) : ℝ :=
  Q d * c d j / ∏ v, scale (principal d j v)

noncomputable def scaledTailCoefficient (Q : D → ℝ) (scale : K → ℝ)
    (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (t : ℝ) (z : Z → ℝ) (d : D) (n : L d) : ℝ :=
  Q d * (t * (weight d n * z (coefficientIndex d n))) /
    ∏ k ∈ (exponent d n).support, scale k ^ exponent d n k

noncomputable def scaledProductArrayJet (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d))
    (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (principal : ∀ d, B d → Fin (h d) → K) (coefficientIndex : ∀ d, L d → Z)
    (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (Q : D → ℝ) (scale : K → ℝ) (constant : D → ℝ)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) : (Σ d, O d) → ℝ :=
  rawProductArrayJet h sets terms exponent principal
    (scaledPrincipalCoefficient h Q scale principal c)
    (scaledTailCoefficient Q scale weight exponent coefficientIndex t z)
    (fun d => Q d * constant d) Q (fun vertex k => scale k * normalizedCubeTuple input z x vertex k)

def booleanConstantJet (sets : ∀ d, O d → Finset α) (constant : D → ℝ) (o : Σ d, O d) : ℝ :=
  if sets o.1 o.2 = ∅ then constant o.1 else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rawProductArrayValue_scaled {D K Z : Type*} {B L : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → K →₀ ℕ) (principal : ∀ d, B d → Fin (h d) → K)
    (coefficientIndex : ∀ d, L d → Z) (c : ∀ d, B d → ℝ)
    (Q : D → ℝ) (scale : K → ℝ) (constant : D → ℝ)
    (hQ : ∀ d, Q d ≠ 0) (hscale : ∀ k, scale k ≠ 0) (t : ℝ) (z : Z → ℝ) (y : K → ℝ) (d : D) :
    rawProductArrayValue h terms exponent principal (scaledPrincipalCoefficient h Q scale principal c)
      (scaledTailCoefficient Q scale weight exponent coefficientIndex t z)
      (fun d => Q d * constant d) (fun k => scale k * y k) d / Q d =
        constant d + (∑ j, c d j * ∏ v, y (principal d j v)) +
          t * (∑ n ∈ terms d, (weight d n * z (coefficientIndex d n)) *
            ∏ k ∈ (exponent d n).support, y k ^ exponent d n k) := by
  classical
  have hc : (Q d * constant d) / Q d = constant d := by field_simp [hQ d]
  have hp : (∑ j, scaledPrincipalCoefficient h Q scale principal c d j *
      ∏ v, scale (principal d j v) * y (principal d j v)) / Q d =
        ∑ j, c d j * ∏ v, y (principal d j v) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    exact normalizedProductTerm _ _ _ _ (hQ d) (fun v => hscale (principal d j v))
  have ht : (∑ n ∈ terms d, scaledTailCoefficient Q scale weight exponent coefficientIndex t z d n *
      ∏ k ∈ (exponent d n).support, (scale k * y k) ^ exponent d n k) / Q d =
        t * (∑ n ∈ terms d, (weight d n * z (coefficientIndex d n)) *
          ∏ k ∈ (exponent d n).support, y k ^ exponent d n k) := by
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [scaledTailCoefficient, normalizedMonomialTerm _ _ _ _ _ (hQ d) hscale]
    ring
  rw [rawProductArrayValue, add_div, add_div, hc, hp, ht]

theorem scaledProductArrayJet_eq {D K Z α : Type*} [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (principal : ∀ d, B d → Fin (h d) → K) (coefficientIndex : ∀ d, L d → Z)
    (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (hinput : ∀ d j v r, input (principal d j v) r = .inr ⟨d, j, v, r⟩)
    (Q : D → ℝ) (scale : K → ℝ) (constant : D → ℝ)
    (hQ : ∀ d, Q d ≠ 0) (hscale : ∀ k, scale k ≠ 0)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) :
    scaledProductArrayJet h c sets terms weight exponent principal coefficientIndex input Q scale constant t z x =
      booleanConstantJet sets constant + coefficientArraySampler h c sets terms weight exponent coefficientIndex input t z x := by
  classical
  funext o
  unfold scaledProductArrayJet rawProductArrayJet
  rw [← booleanCoefficient_div]
  simp_rw [rawProductArrayValue_scaled h terms weight exponent principal coefficientIndex c Q scale constant hQ hscale]
  rw [booleanCoefficient_add, booleanCoefficient_add, booleanCoefficient_const, booleanCoefficient_const_mul]
  have hp : booleanCoefficient (fun vertex => ∑ j, c o.1 j *
      ∏ v, normalizedCubeTuple input z x vertex (principal o.1 j v)) (sets o.1 o.2) =
        jointBooleanSampler h c sets x o := by
    rw [jointBooleanSampler_formula]
    simp only [normalizedCubeTuple, hinput, Sum.elim_inr]
  rw [hp]
  change (if sets o.1 o.2 = ∅ then constant o.1 else 0) + jointBooleanSampler h c sets x o +
      t * normalizedCoefficientTailValue (terms o.1) (weight o.1) (exponent o.1) (coefficientIndex o.1)
        input z x (sets o.1 o.2) = _
  simp only [Pi.add_apply, booleanConstantJet, coefficientArraySampler, add_assoc]

end Erdos3

end

end OAI
