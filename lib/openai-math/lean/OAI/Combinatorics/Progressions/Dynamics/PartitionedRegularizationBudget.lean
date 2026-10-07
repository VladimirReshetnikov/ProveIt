import OAI.Combinatorics.Progressions.Probability.PartitionedProfileMassComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem dependentAxis_card_split {D : Type*} [Fintype D] (V : D → Type*)
    [∀ d, Fintype (V d)] (P : D → Prop) [DecidablePred P] :
    Fintype.card (Σ d : {d // P d}, V d.val) +
      Fintype.card (Σ d : {d // ¬P d}, V d.val) = Fintype.card (Σ d, V d) := by
  simp only [Fintype.card_sigma]
  exact Fintype.sum_subtype_add_sum_subtype P (fun d => Fintype.card (V d))

theorem dependentAxis_card_restrict_le {D : Type*} [Fintype D] (V : D → Type*)
    [∀ d, Fintype (V d)] (P : D → Prop) [DecidablePred P] :
    Fintype.card (Σ d : {d // P d}, V d.val) ≤ Fintype.card (Σ d, V d) := by
  have he := dependentAxis_card_split V P
  omega

theorem nonnegative_axis_sum_restrict_le {D : Type*} [Fintype D]
    (P : D → Prop) [DecidablePred P] (f : D → ℝ) (hf : ∀ d, 0 ≤ f d) :
    (∑ d : {d // P d}, f d.val) ≤ ∑ d, f d := by
  have he := Fintype.sum_subtype_add_sum_subtype P f
  have hn : 0 ≤ ∑ d : {d // ¬P d}, f d.val := Finset.sum_nonneg (fun d _ => hf d.val)
  linarith

theorem partitionedPolynomialParameter_card {D G Z α : Type*}
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] :
    Fintype.card (PolynomialParameter (PartitionedProfileNoiseIndex G Z α B h P)
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d))) =
    Fintype.card (PolynomialParameter (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d))
      (JointBlockParameter B h α)) := by
  have he := dependentAxis_card_split (fun d => BlockParameter (B d) (Fin (h d)) α) P
  change Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) P) +
    Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d)) =
    Fintype.card (JointBlockParameter B h α) at he
  simp only [PolynomialParameter, Fintype.card_option, PartitionedProfileNoiseIndex, Fintype.card_sum]
  change (Fintype.card Z + Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) P) +
      Fintype.card (Σ d, SamplerCoefficientSlot G B h d) +
      Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d))) + 1 =
    (Fintype.card Z + Fintype.card (Σ d, SamplerCoefficientSlot G B h d) +
      Fintype.card (JointBlockParameter B h α)) + 1
  omega

theorem partitionedMassToleranceC2_eq {D G Z α : Type*}
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] (degree : ℕ) (W : ℝ) :
    booleanMassToleranceC2 (B := fun d : {d // ¬P d} => B d.val) (α := α)
      (PartitionedProfileNoiseIndex G Z α B h P) (fun d => h d.val) degree W =
    booleanMassToleranceC2 (B := B) (α := α)
      (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h degree W := by
  unfold booleanMassToleranceC2
  rw [partitionedPolynomialParameter_card]

theorem jointBooleanWeightBudget_restrict_le {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (P : D → Prop) [DecidablePred P] (h : D → ℕ)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (A T : ℝ≥0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 ≤ r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 ≤ κ d) :
    jointBooleanWeightBudget (B := fun d : {d // P d} => B d.val)
      (O := fun d : {d // P d} => O d.val) (α := α)
      (fun d => h d.val) (fun d => C d.val) A T (fun d => r d.val) (fun d => κ d.val) ≤
    jointBooleanWeightBudget (B := B) (O := O) (α := α) h C A T r κ := by
  unfold jointBooleanWeightBudget
  refine nonnegative_axis_sum_restrict_le P (fun d =>
    (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) *
      ((Fintype.card α : ℝ) + 1) ^ 2 * T / r d i) +
    (Fintype.card (BlockParameter (B d) (Fin (h d)) α) : ℝ) * ((A : ℝ) / κ d *
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1)) ?_
  intro d
  exact add_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (by positivity) (hr d i)))
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (div_nonneg A.coe_nonneg (hκ d))
      (productMinorDeterminantDerivativeBound_nonneg _ _ _ _ (hC d) zero_le_one)))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem nnreal_axis_sum_restrict_le {D : Type*} [Fintype D]
    (P : D → Prop) [DecidablePred P] (f : D → ℝ≥0) :
    (∑ d : {d // P d}, f d.val) ≤ ∑ d, f d := by
  calc
    _ ≤ (∑ d : {d // P d}, f d.val) + ∑ d : {d // ¬P d}, f d.val :=
      le_add_of_nonneg_right zero_le
    _ = _ := Fintype.sum_subtype_add_sum_subtype P f

theorem jointBooleanInverseBudget_restrict_le {D α : Type*} [Fintype D] [Fintype α]
    {O : D → Type*} [∀ d, Fintype (O d)]
    (P : D → Prop) [DecidablePred P] (h : D → ℕ) (C κ : D → ℝ) :
    jointBooleanInverseBudget (O := fun d : {d // P d} => O d.val) (α := α)
      (fun d => h d.val) (fun d => C d.val) (fun d => κ d.val) ≤
    jointBooleanInverseBudget (O := O) (α := α) h C κ := by
  unfold jointBooleanInverseBudget
  exact nnreal_axis_sum_restrict_le P (fun d => Real.toNNReal
    (productMinorInverseBound (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 (κ d)))

theorem jointBooleanDerivativeBudget_restrict_le {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (P : D → Prop) [DecidablePred P] (h : D → ℕ) (C : D → ℝ) :
    jointBooleanDerivativeBudget (B := fun d : {d // P d} => B d.val)
      (O := fun d : {d // P d} => O d.val) (α := α) (fun d => h d.val) (fun d => C d.val) ≤
    jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C := by
  unfold jointBooleanDerivativeBudget
  exact nnreal_axis_sum_restrict_le P (fun d => Real.toNNReal
    (productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1))

theorem jointBooleanTranslationBudget_restrict_le {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (P : D → Prop) [DecidablePred P] (h : D → ℕ) (C : D → ℝ) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 ≤ r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 ≤ κ d) :
    jointBooleanTranslationBudget (B := fun d : {d // P d} => B d.val)
      (O := fun d : {d // P d} => O d.val) (α := α)
      (fun d => h d.val) (fun d => C d.val) A T (fun d => r d.val) (fun d => κ d.val) ≤
    jointBooleanTranslationBudget (B := B) (O := O) (α := α) h C A T r κ := by
  have hK : (jointBooleanInverseBudget (O := fun d : {d // P d} => O d.val) (α := α)
      (fun d => h d.val) (fun d => C d.val) (fun d => κ d.val) : ℝ) ≤
      jointBooleanInverseBudget (O := O) (α := α) h C κ := by
    exact_mod_cast jointBooleanInverseBudget_restrict_le (O := O) (α := α) P h C κ
  have hH : (jointBooleanDerivativeBudget (B := fun d : {d // P d} => B d.val)
      (O := fun d : {d // P d} => O d.val) (α := α) (fun d => h d.val) (fun d => C d.val) : ℝ) ≤
      jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C := by
    exact_mod_cast jointBooleanDerivativeBudget_restrict_le (B := B) (O := O) (α := α) P h C
  have hS := jointBooleanWeightBudget_restrict_le (O := O) (α := α) P h C hC A T r hr κ hκ
  have hS0 := jointBooleanWeightBudget_nonneg (O := O) (α := α) h C hC A T r hr κ hκ
  have hSP0 := jointBooleanWeightBudget_nonneg
    (B := fun d : {d // P d} => B d.val) (O := fun d : {d // P d} => O d.val) (α := α)
    (fun d => h d.val) (fun d => C d.val) (fun d => hC d.val) A T
    (fun d => r d.val) (fun d i => hr d.val i) (fun d => κ d.val) (fun d => hκ d.val)
  have hI : (Fintype.card (JointBlockParameter (fun d : {d // P d} => B d.val)
      (fun d => h d.val) α) : ℝ) ≤ Fintype.card (JointBlockParameter B h α) := by
    exact_mod_cast dependentAxis_card_restrict_le (fun d => BlockParameter (B d) (Fin (h d)) α) P
  have hO : (Fintype.card (Σ d : {d // P d}, O d.val) : ℝ) ≤ Fintype.card (Σ d, O d) := by
    exact_mod_cast dependentAxis_card_restrict_le O P
  unfold jointBooleanTranslationBudget
  apply Real.toNNReal_mono
  gcongr

theorem jointBooleanRegularizationBudget_restrict_le {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (P : D → Prop) [DecidablePred P] (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (A T : ℝ≥0) (η : D → ℝ) (hη : ∀ d, 0 < η d) :
    jointBooleanRegularizationBudget (B := fun d : {d // P d} => B d.val)
      (O := fun d : {d // P d} => O d.val) (α := α)
      (fun d => h d.val) (fun d => c₀ d.val) (fun d => C d.val) A T (fun d => η d.val) ≤
    jointBooleanRegularizationBudget (B := B) (O := O) (α := α) h c₀ C A T η :=
  jointBooleanTranslationBudget_restrict_le P h C hC A T
    (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2))
    (fun d _ => (scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d))).le)
    (fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d))
    (fun d => (canonicalCubeMinorThreshold_pos Unit (O d) α (hh d) (hc₀ d) (hη d)).le)

end Erdos3

end

end OAI
