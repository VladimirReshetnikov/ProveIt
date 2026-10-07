import OAI.Combinatorics.Progressions.Sampling.ShiftedSmoothFiniteGridLaw

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

private theorem decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

noncomputable def shiftedSmoothSublevelConstant (N d : ℕ) : ℝ :=
  (2 : ℝ) ^ N * (2 ^ N * multivariateSublevelConstant N d)

noncomputable def shiftedSmoothSublevelThreshold (N d count : ℕ) (η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * d) count (shiftedSmoothSublevelConstant N d)
    ((d + 1 : ℝ) ^ N) η

theorem shiftedSmoothSublevelConstant_nonneg {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 ≤ shiftedSmoothSublevelConstant N d := by
  unfold shiftedSmoothSublevelConstant
  exact mul_nonneg (by positivity)
    (mul_nonneg (by positivity) (multivariateSublevelConstant_pos hN d).le)

theorem shiftedSmoothSublevelThreshold_pos {N : ℕ} (hN : 0 < N) (d count : ℕ)
    {η : ℝ} (hη : 0 < η) : 0 < shiftedSmoothSublevelThreshold N d count η :=
  polynomialSublevelThreshold_pos _ _ (shiftedSmoothSublevelConstant_nonneg hN d)
    (by positivity) hη

theorem shiftedSmoothSublevelThreshold_le_half {N : ℕ} (hN : 0 < N) (d count : ℕ)
    {η : ℝ} (hη : 0 < η) : shiftedSmoothSublevelThreshold N d count η ≤ 1 / 2 :=
  polynomialSublevelThreshold_le_half _ _ (shiftedSmoothSublevelConstant_nonneg hN d)
    (by positivity) hη

theorem shiftedSmoothProduct_polynomial_sublevel {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (P : MvPolynomial (Fin N) ℝ) (hdeg : ∀ i, P.degreeOf i ≤ d)
    (K u : ℝ) (hK : 0 ≤ K) (hu : 0 < u)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : 1 ≤ |MvPolynomial.eval x₀ P|) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability
      (fun k => |MvPolynomial.eval (rectangularLatticePoint a S k.val) P| ≤ u) ≤
      shiftedSmoothSublevelConstant N d *
        ((u + K * δ) * (d + 1 : ℝ) ^ N) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  have h := shiftedPolynomial_grid_sublevel_bound_of_value hN hd
    (shiftedSmoothProductFiniteWeights a S hS hZ) Subtype.val Subtype.val_injective
    a S hS hδ hδ1 hmesh (rectangularWeightIndices_normalized_bound a S hS)
    P hdeg (2 ^ N) K u (by positivity) hK hu
    (fun k => by simpa only [Fintype.card_fin] using
      shiftedSmoothProductFiniteWeights_point_le a S hS hZ hlarge k)
    hLip x₀ hx₀ hval
  simpa only [shiftedSmoothSublevelConstant, mul_assoc] using h

theorem shiftedSmoothProduct_polynomial_family_threshold {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {T : Type*} [Fintype T]
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hmesh : ∀ i, 1 / S i ≤ δ)
    (P : T → MvPolynomial (Fin N) ℝ) (hdeg : ∀ t i, (P t).degreeOf i ≤ d)
    (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ t x y, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x (P t) - MvPolynomial.eval y (P t)| ≤ K * ‖x - y‖)
    (x₀ : T → Fin N → ℝ) (hx₀ : ∀ t i, |x₀ t i| ≤ 1)
    (hval : ∀ t, 1 ≤ |MvPolynomial.eval (x₀ t) (P t)|)
    (hsmall : K * δ ≤ shiftedSmoothSublevelThreshold N d (Fintype.card T) η) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ t, |MvPolynomial.eval (rectangularLatticePoint a S k) (P t)| ≤
        shiftedSmoothSublevelThreshold N d (Fintype.card T) η)) true).toReal ≤ η / 2 := by
  let κ := shiftedSmoothSublevelThreshold N d (Fintype.card T) η
  let C := shiftedSmoothSublevelConstant N d
  let scale := (d + 1 : ℝ) ^ N
  have hκ : 0 < κ := shiftedSmoothSublevelThreshold_pos hN d _ hη
  have hC : 0 ≤ C := shiftedSmoothSublevelConstant_nonneg hN d
  have hs : 0 ≤ scale := by positivity
  simp only [decide_eq_classical]
  rw [← shiftedSmoothProductFiniteWeights_event_eq_map a S hS hZ]
  apply ((shiftedSmoothProductFiniteWeights a S hS hZ).eventProbability_union_bound _
    (fun t k => |MvPolynomial.eval (rectangularLatticePoint a S k.val) (P t)| ≤ κ)
    (fun _ h => h)).trans
  calc
    _ ≤ ∑ _t : T, C * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro t _
      apply (shiftedSmoothProduct_polynomial_sublevel hN hd a S hS hZ hlarge hδ hδ1 hmesh
        (P t) (hdeg t) K κ hK hκ (hLip t) (x₀ t) (hx₀ t) (hval t)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow
      · exact mul_nonneg (add_nonneg hκ.le (mul_nonneg hK hδ)) hs
      · exact mul_le_mul_of_nonneg_right (by dsimp only [κ] at *; linarith) hs
      · positivity
    _ = (Fintype.card T : ℝ) * C * (2 * κ * scale) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    _ ≤ η / 2 := polynomialSublevelThreshold_total_bound (Nat.mul_pos hN hd) hC hs hη

end Erdos3

end

end OAI
