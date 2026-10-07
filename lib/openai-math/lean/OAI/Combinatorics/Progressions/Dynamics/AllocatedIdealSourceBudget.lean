import OAI.Combinatorics.Progressions.Estimates.AllocatedSourceNormalization
import OAI.Combinatorics.Progressions.Polynomial.AllocatedIdealScalePolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

def allocatedIdealSourceBudget {A : Type*} [Semiring A]
    (m : ℕ) (D p e w E : A) : A :=
  1 + 2 * D + p + allocatedIdealScaleLog m D p e w E

theorem allocatedIdealSourceBudget_bounds (m : ℕ) {D p e w E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    let P := allocatedIdealSourceBudget m D p e w E
    1 ≤ P ∧ D ≤ P ∧ p ≤ P ∧ allocatedIdealScaleLog m D p e w E ≤ P ∧
      2 * D + allocatedIdealScaleLog m D p e w E ≤ P := by
  have h := allocatedIdealScaleInput_bounds m hD hp he hw hE
  have hL := h.2.1.trans h.2.2.2.2.2
  dsimp only [allocatedIdealSourceBudget]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem exists_allocatedIdealSourceBudget_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {D p e w E : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ e → 0 ≤ w → 0 ≤ E →
      allocatedIdealSourceBudget m D p e w E ≤ (D + p + e + w + E + a) ^ a := by
  obtain ⟨b, _, hb⟩ := exists_allocatedIdealScaleLog_bound m
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget
    (1 + 3 * Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b)
  refine ⟨a, ha, ?_⟩
  intro D p e w E hD hp he hw hE
  have hscale := hb hD hp he hw hE
  have hbound : 1 + 3 * (D + p + e + w + E) + (D + p + e + w + E + b) ^ b ≤
      (D + p + e + w + E + a) ^ a := by
    simpa [Polynomial.eval₂_pow] using hpoly (D + p + e + w + E) (by positivity)
  unfold allocatedIdealSourceBudget
  linarith

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

include o in
theorem allocatedIdealSource_numerics {D p e w E : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (C V : Fin m → ℝ≥0) (hC : ∀ j, (C j : ℝ) ≤ Real.exp p)
    (hV : ∀ j, (V j : ℝ) ≤ Real.exp p) :
    AllocatedSourceNumerics B U b (allocatedIdealScale (G := G) B U b hR hσ D p e w E)
      C V (allocatedIdealSourceBudget m D p e w E) := by
  let S := allocatedIdealScale (G := G) B U b hR hσ D p e w E
  let L := allocatedIdealScaleLog m D p e w E
  let P := allocatedIdealSourceBudget m D p e w E
  obtain ⟨hP1, hDP, hpP, hLP, hrootP⟩ :=
    allocatedIdealSourceBudget_bounds m hdim.nonneg hp he hw hE
  have hP : 0 ≤ P := (by norm_num : (0 : ℝ) ≤ 1).trans hP1
  have hS : (S.value : ℝ) ≤ Real.exp L :=
    allocatedIdealScale_upper B U b hR hσ hdim hp he hw hE hRi hσi
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * D := by
    change (Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ 2 * D
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith [hdim.kernel_variables, hdim.tuples]
  have hI (j : Fin m) : (Fintype.card (I j) : ℝ) ≤ D := by
    have hi : Function.Injective (fun i : I j => (⟨j, Sum.inl i⟩ : LayerSamplerAxis I n)) := by
      intro a b hab
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Sum.inl.injEq] using hab
    exact (Nat.cast_le.mpr (Fintype.card_le_of_injective _ hi)).trans hdim.axes
  have hL0 : 0 ≤ L := by
    have h := allocatedIdealScaleInput_bounds m hdim.nonneg hp he hw hE
    exact h.2.1.trans h.2.2.2.2.2
  have hvarsP : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P := by
    exact hvars.trans (by dsimp [P, allocatedIdealSourceBudget]; linarith)
  have hroot : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ Real.exp P := by
    simp only [allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add]
    calc
      _ ≤ Real.exp (2 * D) * Real.exp L := mul_le_mul
        (hvars.trans (by linarith [Real.add_one_le_exp (2 * D)])) hS
        (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * D + L) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hrootP
  have hExp := Real.exp_le_exp.mpr hpP
  exact {
    nonneg := hP
    degree := hdim.degree.trans hDP
    variable_count := hvarsP
    length := hS.trans (Real.exp_le_exp.mpr hLP)
    radius_inv := fun j => (hRi j).trans hExp
    width_inv := fun j => (hσi j).trans hExp
    coefficients := fun j => (hdim.coefficients j).trans hDP
    real_axes := fun j => (hI j).trans hDP
    integer_axes := fun j => (hdim.integer_axes B j).trans hDP
    ambient_axes := fun j => (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U b o j)).trans
      (hdim.axes.trans hDP)
    profile := (hdim.profile.trans hDP).trans (by linarith [Real.add_one_le_exp P])
    chart := fun j => (hC j).trans hExp
    covolume := fun j => (hV j).trans hExp
    root := hroot }

end Erdos3.VectorPolynomial

end

end OAI
