import OAI.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
import OAI.Combinatorics.Progressions.Probability.ScalarCubeDensityBudget

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def scalarCubeProductBoundaryRadius (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] (η : ℝ) : ℝ :=
  η / (scalarCubeBoundaryConstant α * ((Fintype.card ι : ℝ) + 1))

theorem scalarCubeProductBoundaryRadius_pos (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] {η : ℝ} (hη : 0 < η) : 0 < scalarCubeProductBoundaryRadius ι α η :=
  div_pos hη (mul_pos (scalarCubeBoundaryConstant_pos α) (by positivity))

theorem scalarCubeProductBoundaryRadius_loss (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] {η : ℝ} (hη : 0 < η) :
    scalarCubeBoundaryConstant α * ∑ _i : ι, scalarCubeProductBoundaryRadius ι α η ≤ η := by
  have hC := scalarCubeBoundaryConstant_pos α
  have hm : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have he : scalarCubeBoundaryConstant α *
      ((Fintype.card ι : ℝ) * scalarCubeProductBoundaryRadius ι α η) =
      η * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) + 1) := by
    unfold scalarCubeProductBoundaryRadius
    field_simp
  rw [he]
  apply (div_le_iff₀ hm).mpr
  nlinarith

noncomputable def scalarCubeProductDerivativeConstant (α : Type*) [Fintype α]
    [DecidableEq α] (A : ℝ≥0) : ℝ :=
  ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A *
    scalarCubeBoundaryConstant α

theorem scalarCubeProductBoundaryRadius_derivative (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] (A : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (∑ _i : ι, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A /
      scalarCubeProductBoundaryRadius ι α η) ≤
      scalarCubeProductDerivativeConstant α A * ((Fintype.card ι : ℝ) + 1) ^ 2 / η := by
  have hC := scalarCubeBoundaryConstant_pos α
  have hm : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have he : (∑ _i : ι, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A /
      scalarCubeProductBoundaryRadius ι α η) =
      scalarCubeProductDerivativeConstant α A * (Fintype.card ι : ℝ) *
        ((Fintype.card ι : ℝ) + 1) / η := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      scalarCubeProductBoundaryRadius, scalarCubeProductDerivativeConstant]
    field_simp
  rw [he]
  have hB : 0 ≤ scalarCubeProductDerivativeConstant α A := by
    unfold scalarCubeProductDerivativeConstant
    positivity
  apply div_le_div_of_nonneg_right _ hη.le
  have h := mul_le_mul_of_nonneg_left
    (show (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 1) ≤
      ((Fintype.card ι : ℝ) + 1) ^ 2 by nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]) hB
  simpa only [mul_assoc] using h

theorem exists_scalarCubeProductWeight_with_error (ι α : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition)
    {η : ℝ} (hη : 0 < η) :
    ∃ w : (ι → Option α → ℝ) → ℝ,
      ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ tsupport w ⊆ scalarCubeProductDomain ι α ∧
      (∀ x, 0 ≤ w x) ∧ 1 - η ≤ (∫ x, w x) ∧ (∫ x, |w x|) ≤ 1 ∧
      (∑ i, ∑ j : Option α, ∫ x, |fderiv ℝ w x (Pi.single i (Pi.single j 1))|) ≤
        scalarCubeProductDerivativeConstant α A * ((Fintype.card ι : ℝ) + 1) ^ 2 / η := by
  let r : ι → ℝ := fun _ => scalarCubeProductBoundaryRadius ι α η
  have hr : ∀ i, 0 < r i := fun _ => scalarCubeProductBoundaryRadius_pos ι α hη
  have hs := scalarCubeProductWeight_spec (α := α) r hr
  refine ⟨scalarCubeProductWeight α r, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_,
    hs.2.2.2.2, (scalarCubeProductWeight_derivative_budget r hr A hLip).trans
      (scalarCubeProductBoundaryRadius_derivative ι α A hη)⟩
  have hl := scalarCubeProductWeight_mass_lower (α := α) r hr
  have he := scalarCubeProductBoundaryRadius_loss ι α hη
  exact (sub_le_sub_left he 1).trans hl

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def scalarCubeBoundaryLog (q : ℕ) : ℝ := ((q : ℝ)+1)^2+2*q+2
def scalarCubeDerivativeLog (q : ℕ) (P : ℝ) : ℝ := P+3*q+1+scalarCubeBoundaryLog q

theorem scalarCubeBoundaryConstant_le_exp (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeBoundaryConstant I ≤ Real.exp (scalarCubeBoundaryLog (Fintype.card I)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ)^2 := by norm_num
      _ ≤ (Real.exp 1)^2 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hd := scalarCubeDomainDensity_le_exp I
  have hd0 := (scalarCubeDomainDensity_pos I).le
  unfold scalarCubeBoundaryConstant
  calc
    _ ≤ Real.exp 2*Real.exp (((Fintype.card I : ℝ)+1)^2)*((Real.exp 1)^Fintype.card I)^2 := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold scalarCubeBoundaryLog
      ring

theorem scalarCubeProductBoundaryRadius_inverse_le_exp (J I : Type*)
    [Fintype J] [Fintype I] [DecidableEq I] {η E : ℝ}
    (hη : 0 < η) (hηE : η⁻¹ ≤ Real.exp E) :
    (scalarCubeProductBoundaryRadius J I η)⁻¹ ≤
      Real.exp (scalarCubeBoundaryLog (Fintype.card I)+Fintype.card J+E) := by
  have hC := scalarCubeBoundaryConstant_le_exp I
  have hC0 := (scalarCubeBoundaryConstant_pos I).le
  have hn : (Fintype.card J : ℝ)+1 ≤ Real.exp (Fintype.card J) := Real.add_one_le_exp _
  rw [scalarCubeProductBoundaryRadius, inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (scalarCubeBoundaryLog (Fintype.card I))*Real.exp (Fintype.card J)*Real.exp E := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]

theorem scalarCubeProductDerivativeConstant_le_exp (I : Type*) [Fintype I] [DecidableEq I]
    (A : ℝ≥0) {P : ℝ} (hA : (A : ℝ) ≤ Real.exp P) :
    scalarCubeProductDerivativeConstant I A ≤ Real.exp (scalarCubeDerivativeLog (Fintype.card I) P) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq : (Fintype.card I : ℝ)+1 ≤ Real.exp (Fintype.card I) := Real.add_one_le_exp _
  have hC := scalarCubeBoundaryConstant_le_exp I
  have hC0 := (scalarCubeBoundaryConstant_pos I).le
  unfold scalarCubeProductDerivativeConstant
  push_cast
  calc
    _ ≤ (Real.exp 1*(Real.exp 1)^Fintype.card I)*(Real.exp (Fintype.card I))^2*
        Real.exp P*Real.exp (scalarCubeBoundaryLog (Fintype.card I)) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold scalarCubeDerivativeLog
      ring

end Erdos3

end

end OAI
