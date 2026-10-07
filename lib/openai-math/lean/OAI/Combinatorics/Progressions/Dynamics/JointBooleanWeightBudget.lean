import OAI.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight
import OAI.Combinatorics.Progressions.Estimates.SigmaWeightDerivative

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem booleanCubeGoodWeight_derivative_budget {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B) {h : ℕ}
    (v : Fin h) (sel : J → O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ j o, |c j (block j o)| ≤ C)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i) :
    let G := productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h C 1
    (∑ z : BlockParameter B (Fin h) α,
      ∫ a, |fderiv ℝ (booleanCubeGoodWeight c sets block v sel ψ r κ) a (Pi.single z 1)|) ≤
      (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r i) +
        (Fintype.card (BlockParameter B (Fin h) α) : ℝ) * ∑ j, ((A : ℝ) / κ j) * G := by
  let G : ℝ≥0 := ⟨productMinorDeterminantDerivativeBound
    (Fintype.card (BlockParameter B (Fin h) α)) (Fintype.card O) (Fintype.card α) h C 1,
    productMinorDeterminantDerivativeBound_nonneg _ _ _ _ hC zero_le_one⟩
  let d := fun j => booleanCubeDeterminant (c j) sets (block j) v (sel j)
  have hd := fun j => booleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j)
  have hder (j) (x) (hx : x ∈ scalarCubeProductDomain (B × Fin h) α) :
      ‖fderiv ℝ (d j) x‖ ≤ G :=
    booleanCubeDeterminant_fderiv_norm_le (c j) sets (block j) v (sel j) hcard hC (hc j) x hx
  have hbudget := scalarCubeGoodWeight_derivative_budget ψ hψ hrange A T hLip hTransition
    r hr κ hκ d hd (fun _ => G) hder
  have hwn : ContDiff ℝ 1 (scalarCubeGoodWeight α ψ r κ d) :=
    (scalarCubeProductWeight_spec (α := α) r hr).1.mul
      ((sublevelCutoffProduct_smooth ψ hψ κ d hd).of_le (by norm_num))
  change (∑ z, ∫ a, |fderiv ℝ (blockCubeWeight (scalarCubeGoodWeight α ψ r κ d)) a (Pi.single z 1)|) ≤ _
  rw [blockCubeWeight_derivative_sum _ hwn]
  have hdim : (Fintype.card (B × Fin h) : ℝ) * ((Fintype.card α : ℝ) + 1) =
      (Fintype.card (BlockParameter B (Fin h) α) : ℝ) := by
    simp only [BlockParameter, Fintype.card_prod, Fintype.card_option, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring
  rw [hdim] at hbudget
  exact hbudget

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointBooleanGoodWeight_derivative_budget {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) :
    let n := fun d => Fintype.card (BlockParameter (B d) (Fin (h d)) α)
    let G := fun d => productMinorDeterminantDerivativeBound (n d) (Fintype.card (O d))
      (Fintype.card α) (h d) (C d) 1
    (∑ s : JointBlockParameter B h α, ∫ x,
      |fderiv ℝ (jointBooleanGoodWeight c sets block v sel ψ r κ) x (Pi.single s 1)|) ≤
      ∑ d, ((∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r d i) +
        (n d : ℝ) * ((A : ℝ) / κ d * G d)) := by
  have hs (d : D) := booleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) ψ hψ hrange hzero (r d) (hr d)
    (fun _ => κ d) (fun _ => hκ d)
  apply (sigmaAxisWeight_derivative_sum_le _ (fun d => (hs d).1)
    (fun d => (hs d).2.2.2.1)).trans
  apply Finset.sum_le_sum
  intro d _
  have hb := booleanCubeGoodWeight_derivative_budget (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (hcard d) (hC d) (fun _ => hc d)
    ψ hψ hrange A T hLip hTransition (r d) (hr d) (fun _ => κ d) (fun _ => hκ d)
  simpa only [Fintype.sum_unique] using hb

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanWeightBudget (h : D → ℕ) (C : D → ℝ) (A T : ℝ≥0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ) : ℝ :=
  ∑ d, ((∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) *
    ((Fintype.card α : ℝ) + 1) ^ 2 * T / r d i) +
    (Fintype.card (BlockParameter (B d) (Fin (h d)) α) : ℝ) * ((A : ℝ) / κ d *
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1))

theorem jointBooleanWeightBudget_nonneg (h : D → ℕ) (C : D → ℝ) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 ≤ r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 ≤ κ d) :
    0 ≤ jointBooleanWeightBudget (O := O) (α := α) h C A T r κ := by
  apply Finset.sum_nonneg
  intro d _
  exact add_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (by positivity) (hr d i)))
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (div_nonneg A.coe_nonneg (hκ d))
      (productMinorDeterminantDerivativeBound_nonneg _ _ _ _ (hC d) zero_le_one)))

end Erdos3

end

end OAI
