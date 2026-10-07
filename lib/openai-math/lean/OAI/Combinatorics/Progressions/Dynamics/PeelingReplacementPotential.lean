import OAI.Combinatorics.Progressions.Estimates.PeelingCost

namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem potentialCost_zero (B : Finset G) (f : G → ℝ) (cs : List (Finset G)) :
    potentialCost B 0 f cs = 0 := by
  induction cs generalizing f with
  | nil => rfl
  | cons C cs ih =>
    simp only [potentialCost, mul_zero, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), zero_add]
    exact ih (remainder C f)

theorem Chain.potential_budget_nonneg {B : Finset G} {Admissible : Finset G → Prop}
    {K kappa v : ℝ} {f g : G → ℝ} {cs : List (Finset G)}
    (h : Chain B Admissible K kappa f g cs) (hK : 0 < K) (hkappa : 0 < kappa) (hv : 0 ≤ v)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * potentialCost B v f cs ≤
      ((𝔼 x ∈ B, f x) * v) ^ (1 / 4 : ℝ) - ((𝔼 x ∈ B, g x) * v) ^ (1 / 4 : ℝ) := by
  rcases hv.eq_or_lt with hv | hv
  · subst v
    simp only [potentialCost_zero, mul_zero, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), sub_self, le_refl]
  · exact h.potential_budget hK hkappa hv hf hsupport

theorem pair_potential_budget {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Chain B Admissible K kappa f f' cs) (hG : Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) *
        (potentialCost B (𝔼 x ∈ B, g x) f cs + potentialCost B (𝔼 x ∈ B, f' x) g ds) ≤
      ((𝔼 x ∈ B, f x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) -
        ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) := by
  have h₁ := hF.potential_budget_nonneg hK hkappa (Finset.expect_nonneg (s := B) (fun x _ => hg x)) hf hfsupport
  have h₂ := hG.potential_budget_nonneg hK hkappa
    (Finset.expect_nonneg (s := B) (fun x _ => (hF.bounds hf x).1)) hg hgsupport
  have h₂' : (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * potentialCost B (𝔼 x ∈ B, f' x) g ds ≤
      ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) -
        ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) := by
    simpa only [mul_comm] using h₂
  nlinarith

theorem pair_coefficient_budget {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Chain B Admissible K kappa f f' cs) (hG : Chain B Admissible K kappa g g' ds)
    (hK : 0 ≤ K) (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    (K * kappa) * (coefficientCost B cs + coefficientCost B ds) ≤
      ((𝔼 x ∈ B, f x) - 𝔼 x ∈ B, f' x) + ((𝔼 x ∈ B, g x) - 𝔼 x ∈ B, g' x) := by
  have h₁ := hF.coefficient_budget hK hfsupport
  have h₂ := hG.coefficient_budget hK hgsupport
  nlinarith

end Erdos3.Peeling

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
theorem coefficientCost_nonneg (B : Finset G) (cs : List (Finset G)) :
    0 ≤ coefficientCost B cs := by
  induction cs with
  | nil => simp [coefficientCost]
  | cons C cs ih =>
    simp only [coefficientCost, List.map_cons, List.sum_cons] at ih ⊢
    exact add_nonneg (by positivity) ih

theorem pair_coefficientCost_le {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Chain B Admissible K kappa f f' cs) (hG : Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    coefficientCost B cs + coefficientCost B ds ≤
      ((𝔼 x ∈ B, f x) + 𝔼 x ∈ B, g x) / (K * kappa) := by
  have h := pair_coefficient_budget hF hG hK.le hfsupport hgsupport
  have hf' := Finset.expect_nonneg (s := B) (fun x _ => (hF.bounds hf x).1)
  have hg' := Finset.expect_nonneg (s := B) (fun x _ => (hG.bounds hg x).1)
  apply (le_div_iff₀ (mul_pos hK hkappa)).mpr
  nlinarith

theorem weighted_pair_error_le {B : Finset G} {Admissible : Finset G → Prop} {K kappa epsilon : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Chain B Admissible K kappa f f' cs) (hG : Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hepsilon : 0 ≤ epsilon)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    epsilon * (coefficientCost B cs + coefficientCost B ds) ≤
      epsilon * (((𝔼 x ∈ B, f x) + 𝔼 x ∈ B, g x) / (K * kappa)) :=
  mul_le_mul_of_nonneg_left (pair_coefficientCost_le hF hG hK hkappa hf hg hfsupport hgsupport) hepsilon

theorem contraction_after_peeling {P remainder initial a rho : ℝ}
    (hP : 0 ≤ P) (ha : 2 ≤ a) (hrho : 1 / 2 ≤ rho)
    (hbudget : a * P + remainder ≤ initial) :
    P + rho * remainder ≤ rho * initial := by
  have hrho0 : 0 ≤ rho := by linarith
  have hprod : 1 ≤ rho * a := by
    have h := mul_le_mul hrho ha (by norm_num : (0 : ℝ) ≤ 2) hrho0
    norm_num at h
    exact h
  nlinarith [mul_le_mul_of_nonneg_right hprod hP,
    mul_le_mul_of_nonneg_left hbudget hrho0]

end Erdos3.Peeling

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def replacementPotentialSum (A Q : Finset G) (shape : Finset G → Finset G)
    (g : G → ℝ) : (G → ℝ) → List (Finset G) → ℝ
  | _, [] => 0
  | f, D :: ds => (D.card : ℝ) / A.card * replacementPotential D Q (shape D) f g +
      replacementPotentialSum A Q shape g (Peeling.remainder D f) ds

theorem replacementPotentialSum_nonneg (A Q : Finset G) (shape : Finset G → Finset G)
    (g : G → ℝ) (hg : ∀ x, 0 ≤ g x) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ds : List (Finset G)) : 0 ≤ replacementPotentialSum A Q shape g f ds := by
  induction ds generalizing f with
  | nil => simp [replacementPotentialSum]
  | cons D ds ih =>
    exact add_nonneg (mul_nonneg (by positivity) (replacementPotential_nonneg D Q (shape D) f g hf hg))
      (ih (Peeling.remainder D f) (Peeling.remainder_nonneg D f hf))

variable [Fintype G]

theorem replacementPotentialSum_le_cost (A Q : Finset G) (hQ : Q.Nonempty)
    (shape : Finset G → Finset G) (g : G → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hgsupport : ∀ x, x ∉ Q → g x = 0) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ds : List (Finset G)) (hshape : ∀ D ∈ ds, (shape D).Nonempty) :
    replacementPotentialSum A Q shape g f ds ≤ Peeling.potentialCost A (𝔼 y ∈ Q, g y) f ds := by
  induction ds generalizing f with
  | nil => simp [replacementPotentialSum, Peeling.potentialCost]
  | cons D ds ih =>
    simp only [replacementPotentialSum, Peeling.potentialCost]
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (replacementPotential_le D Q (shape D) hQ (hshape D (List.mem_cons_self)) f g hf hg hgsupport)
        (by positivity))
      (ih (Peeling.remainder D f) (Peeling.remainder_nonneg D f hf)
        (fun C hC => hshape C (List.mem_cons_of_mem D hC)))

theorem pair_replacement_potential_budget
    {B : Finset G} (hB : B.Nonempty) {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (shape : Finset G → Finset G)
    (hshape : ∀ D, Admissible D → (shape D).Nonempty)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) *
      (replacementPotentialSum B B shape g f cs + replacementPotentialSum B B shape f' g ds) ≤
        ((𝔼 x ∈ B, f x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) -
          ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) := by
  have hfirst := replacementPotentialSum_le_cost B B hB shape g hg hgsupport f hf cs
    (fun D hD => hshape D (hF.admissible_mem D hD))
  have hsecond := replacementPotentialSum_le_cost B B hB shape f'
    (fun x => (hF.bounds hf x).1) (hF.supported hf hfsupport) g hg ds
    (fun D hD => hshape D (hG.admissible_mem D hD))
  exact (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
    (by positivity)).trans (Peeling.pair_potential_budget hF hG hK hkappa hf hg hfsupport hgsupport)

theorem pair_replacement_contraction
    {B : Finset G} (hB : B.Nonempty) {Admissible : Finset G → Prop} {K kappa rho : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hrho : 1 / 2 ≤ rho) (shape : Finset G → Finset G)
    (hshape : ∀ D, Admissible D → (shape D).Nonempty)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    replacementPotentialSum B B shape g f cs + replacementPotentialSum B B shape f' g ds +
      rho * ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) ≤
        rho * ((𝔼 x ∈ B, f x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) := by
  have hbudget := pair_replacement_potential_budget hB hF hG hK hkappa shape hshape hf hg
    hfsupport hgsupport
  apply Peeling.contraction_after_peeling
    (add_nonneg (replacementPotentialSum_nonneg B B shape g hg f hf cs)
      (replacementPotentialSum_nonneg B B shape f' (fun x => (hF.bounds hf x).1) g hg ds))
    hKfactor hrho
  linarith

end Erdos3.CellRefinement

end

end OAI
