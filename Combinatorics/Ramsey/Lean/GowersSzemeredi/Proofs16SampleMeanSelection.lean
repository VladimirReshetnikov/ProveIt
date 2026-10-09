import GowersSzemeredi.Proofs16SampleRetention

/-! A finite weighted-average selection keeps many indices, few bad tuples,
and avoids a collision event simultaneously. The density retained does
not depend on the allowed bad-tuple fraction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_sample_of_mean_bounds {E : Type*} [Fintype E] [Nonempty E]
    (n P : Nat) (hn : 0 < n) (hP : 0 < P)
    (retained bad : E → Nat) (collision : E → Prop)
    {a q p epsilon : Real} (ha : 0 < a) (he : 0 < epsilon)
    (hbound : ∀ e, retained e ≤ n)
    (hret : a*n*Fintype.card E ≤ ∑ e, (retained e : Real))
    (hbad : ∑ e, (bad e : Real) ≤ q*P*Fintype.card E)
    (hcollision : ((Finset.univ.filter collision).card : Real) ≤ p*Fintype.card E)
    (hbadBudget : 2*q/epsilon ≤ a/4) (hcollisionBudget : 2*p ≤ a/4) :
    ∃ e : E, ¬ collision e ∧ a/2*n ≤ (retained e : Real) ∧
      (bad e : Real) ≤ epsilon/2*P := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  let score : E → Real := fun e => (retained e : Real)/n -
    (2/epsilon)*((bad e : Real)/P) - if collision e then 2 else 0
  have hretNorm : a*Fintype.card E ≤ ∑ e, (retained e : Real)/n := by
    calc
      a*Fintype.card E = (a*n*Fintype.card E)/n := by field_simp
      _ ≤ (∑ e, (retained e : Real))/n := div_le_div_of_nonneg_right hret hnR.le
      _ = _ := Finset.sum_div _ _ _
  have hbadNorm : ∑ e, (bad e : Real)/P ≤ q*Fintype.card E := by
    rw [←Finset.sum_div]
    calc
      (∑ e, (bad e : Real))/P ≤ (q*P*Fintype.card E)/P := div_le_div_of_nonneg_right hbad hPR.le
      _ = _ := by field_simp
  have hbadPenalty : (2/epsilon)*(∑ e, (bad e : Real)/P) ≤ a/4*Fintype.card E := by
    calc
      _ ≤ (2/epsilon)*(q*Fintype.card E) := mul_le_mul_of_nonneg_left hbadNorm (by positivity)
      _ = (2*q/epsilon)*Fintype.card E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbadBudget (Nat.cast_nonneg _)
  have hcollisionPenalty : ∑ e : E, (if collision e then (2 : Real) else 0) =
      2*((Finset.univ.filter collision).card : Real) := by
    rw [Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> norm_num
  have hcollisionPenaltyBound : 2*((Finset.univ.filter collision).card : Real) ≤
      a/4*Fintype.card E := by
    calc
      _ ≤ 2*(p*Fintype.card E) := mul_le_mul_of_nonneg_left hcollision (by norm_num)
      _ = (2*p)*Fintype.card E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcollisionBudget (Nat.cast_nonneg _)
  have hscoreSum : a/2*Fintype.card E ≤ ∑ e, score e := by
    simp only [score, Finset.sum_sub_distrib, ←Finset.mul_sum]
    rw [hcollisionPenalty]
    linarith
  have hconstant : ∑ _e : E, a/2 ≤ ∑ e, score e := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hscoreSum
  obtain ⟨e, _, heScore⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hconstant
  have heScorePos : 0 < score e := (half_pos ha).trans_le heScore
  have hretBound : (retained e : Real)/n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hbound e)
  have hbadNonneg : 0 ≤ (2/epsilon)*((bad e : Real)/P) := by positivity
  have hcollisionNonneg : 0 ≤ (if collision e then (2 : Real) else 0) := by split_ifs <;> norm_num
  have hnocollision : ¬ collision e := by
    intro hc
    dsimp only [score] at heScorePos
    rw [if_pos hc] at heScorePos
    linarith
  have hretained : a/2*n ≤ (retained e : Real) := by
    apply (le_div_iff₀ hnR).mp
    dsimp only [score] at heScore
    linarith
  have hbadSmall : (bad e : Real) ≤ epsilon/2*P := by
    have hpen : (2/epsilon)*((bad e : Real)/P) < 1 := by
      dsimp only [score] at heScorePos
      linarith
    have hraw : 2*(bad e : Real) < epsilon*P := by
      have heq : (2/epsilon)*((bad e : Real)/P) = (2*(bad e : Real))/(epsilon*P) := by field_simp
      rw [heq, div_lt_iff₀ (mul_pos he hPR)] at hpen
      simpa only [one_mul] using hpen
    linarith
  exact ⟨e, hnocollision, hretained, hbadSmall⟩

end LeanProofs.GowersSzemeredi
