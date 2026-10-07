import OAI.Combinatorics.Progressions.Dynamics.ReplacementCellPotential

namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

noncomputable def potentialCost (B : Finset G) (v : ℝ) : (G → ℝ) → List (Finset G) → ℝ
  | _, [] => 0
  | f, C :: cs => (C.card : ℝ) / B.card * ((𝔼 x ∈ C, f x) * v) ^ (1 / 4 : ℝ) +
      potentialCost B v (remainder C f) cs

noncomputable def coefficientCost (B : Finset G) (cs : List (Finset G)) : ℝ :=
  (cs.map (fun C => (C.card : ℝ) / B.card)).sum

omit [Fintype G] in
theorem potentialCost_nonneg (B : Finset G) {v : ℝ} (hv : 0 ≤ v)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (cs : List (Finset G)) : 0 ≤ potentialCost B v f cs := by
  induction cs generalizing f with
  | nil => simp [potentialCost]
  | cons C cs ih =>
    exact add_nonneg
      (mul_nonneg (by positivity)
        (Real.rpow_nonneg (mul_nonneg (Finset.expect_nonneg (fun x _ => hf x)) hv) _))
      (ih (remainder C f) (remainder_nonneg C f hf))

theorem Chain.potential_budget {B : Finset G} {Admissible : Finset G → Prop} {K kappa v : ℝ}
    {f g : G → ℝ} {cs : List (Finset G)} (h : Chain B Admissible K kappa f g cs)
    (hK : 0 < K) (hkappa : 0 < kappa) (hv : 0 < v) :
    (∀ x, 0 ≤ f x) → (∀ x, x ∉ B → f x = 0) →
      (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * potentialCost B v f cs ≤
        ((𝔼 x ∈ B, f x) * v) ^ (1 / 4 : ℝ) - ((𝔼 x ∈ B, g x) * v) ^ (1 / 4 : ℝ) := by
  induction h with
  | nil f => intro _ _; simp [potentialCost]
  | @step f g cs C hactive _ hconc _ ih =>
    intro hf hsupport
    have hstep := step_potential_le B C f hf hsupport (hkappa.trans_le hactive) hv hK hconc.le
    have htail := ih (remainder_nonneg C f hf) (remainder_supported B C f hsupport)
    simp only [potentialCost]
    nlinarith

theorem Chain.coefficient_budget {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f g : G → ℝ} {cs : List (Finset G)} (h : Chain B Admissible K kappa f g cs)
    (hK : 0 ≤ K) : (∀ x, x ∉ B → f x = 0) →
      (K * kappa) * coefficientCost B cs ≤ (𝔼 x ∈ B, f x) - 𝔼 x ∈ B, g x := by
  induction h with
  | nil f => intro _; simp [coefficientCost]
  | @step f g cs C hactive _ hconc _ ih =>
    intro hsupport
    have hstep := step_coefficient_le_mass_drop B C f hsupport hK hactive hconc.le
    have htail := ih (remainder_supported B C f hsupport)
    simp only [coefficientCost, List.map_cons, List.sum_cons] at htail ⊢
    nlinarith

end Erdos3.Peeling

end

end OAI
