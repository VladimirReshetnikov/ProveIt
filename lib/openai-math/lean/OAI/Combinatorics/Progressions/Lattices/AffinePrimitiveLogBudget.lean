import OAI.Combinatorics.Progressions.Polynomial.AffineDegreeChoice

namespace OAI

section

namespace Erdos3

noncomputable def affineComparisonTail (ε L T : ℝ) : ℕ :=
  CyclicCrootSisask.spectralIterations (ε / (2 + ε)) (L + 2 * T + 4)

noncomputable def affineComparisonScale (ε L T C : ℝ) : ℝ :=
  L + T + 2 + (affineRemovalDepth T + affineComparisonTail ε L T : ℕ) + C

noncomputable def affineComparisonMoment (P : ℝ) : ℕ :=
  2 * (Nat.floor (P / 2) + 1)

theorem affineComparisonScale_bounds {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    0 ≤ affineComparisonScale ε L T C ∧
    L + T + 2 ≤ affineComparisonScale ε L T C ∧
    ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ) ≤ affineComparisonScale ε L T C ∧
    C ≤ affineComparisonScale ε L T C := by
  have hn : (0 : ℝ) ≤ (affineRemovalDepth T + affineComparisonTail ε L T : ℕ) := Nat.cast_nonneg _
  unfold affineComparisonScale
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem affineComparisonScale_count {ι : Type*} [Fintype ι] {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C) :
    (Fintype.card ι : ℝ) ≤ Real.exp (affineComparisonScale ε L T C) :=
  hcount.trans (Real.exp_le_exp.mpr (affineComparisonScale_bounds (ε := ε) hL hT hC).2.2.2)

theorem affineComparisonMoment_bounds {P : ℝ} (hP : 0 ≤ P) :
    2 ≤ affineComparisonMoment P ∧ Even (affineComparisonMoment P) ∧
    P ≤ (affineComparisonMoment P : ℝ) ∧ (affineComparisonMoment P : ℝ) ≤ P + 2 := by
  unfold affineComparisonMoment
  refine ⟨by omega, even_two_mul _, ?_, ?_⟩
  · have h := Nat.lt_floor_add_one (P / 2)
    push_cast
    linarith
  · have h := Nat.floor_le (by positivity : 0 ≤ P / 2)
    push_cast
    linarith

end Erdos3

end

section

namespace Erdos3

noncomputable def affinePrimitiveLogBudget (P : ℝ) : ℝ := 16 * (P + 3)

theorem affinePrimitiveLogBudget_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affinePrimitiveLogBudget P := by unfold affinePrimitiveLogBudget; positivity

theorem affineRemovalDepth_le_logBudget {T P : ℝ} (hT : 0 ≤ T) (hTP : T ≤ P) :
    (affineRemovalDepth T : ℝ) ≤ 2 * P + 10 := by
  have h := CyclicCrootSisask.spectralIterations_le_logBudget (epsilon := 1) (A := 0)
    (by norm_num) hT le_rfl (by simp)
  change (affineRemovalDepth T : ℝ) ≤ _ at h
  linarith

theorem affineComparisonTail_le_logBudget {epsilon L T P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLP : L ≤ P) (hTP : T ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) :
    (affineComparisonTail epsilon L T : ℝ) ≤ 8 * P + 22 := by
  have h := CyclicCrootSisask.spectralIterations_le_logBudget
    (epsilon := epsilon / (2 + epsilon)) (p := L + 2 * T + 4) (A := P + 2)
    (by positivity) (by positivity) (by positivity)
    (affineAllowance_inverse_le_exp hepsilon hepsilon1 hinverse)
  change (affineComparisonTail epsilon L T : ℝ) ≤ _ at h
  linarith

theorem affineComparisonPrimitive_bounds {epsilon L T C P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) :
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affinePrimitiveLogBudget P ∧
      affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P ∧
      (affineComparisonMoment (affineComparisonScale epsilon L T C) : ℝ) ≤ affinePrimitiveLogBudget P + 2 := by
  have hj := affineRemovalDepth_le_logBudget hT hTP
  have ht := affineComparisonTail_le_logBudget hepsilon hepsilon1 hP hL hT hLP hTP hinverse
  have hsum : ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤
      10 * P + 32 := by push_cast; linarith
  have hs : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P := by
    unfold affineComparisonScale affinePrimitiveLogBudget
    linarith
  refine ⟨?_, hs, ?_⟩
  · unfold affinePrimitiveLogBudget
    linarith
  · have hm := (affineComparisonMoment_bounds (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1).2.2.2
    linarith

end Erdos3

end

end OAI
