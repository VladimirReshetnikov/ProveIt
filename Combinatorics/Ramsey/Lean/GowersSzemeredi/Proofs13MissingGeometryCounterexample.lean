import GowersSzemeredi.Proofs13CoefficientPartition
import GowersSzemeredi.Proofs08AffineFrequencyProgression

/-! A concrete prime-modulus obstruction to the former Lemma 13.9
encoding. A singleton height progression and two-point column progression
satisfy the retained Stage 13.7--13.8 data but cannot support the strictly
larger-than-one height progression required by Stage 13.9. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

private theorem countWhere_pos_of_witness {X : Type*} [Fintype X]
    (p : X → Prop) (x : X) (hx : p x) : 0 < countWhere p := by
  classical
  unfold countWhere
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

private def bad139Context : Section13Context 2 where
  A := {(0, 0)}
  phi := fun _ => 0
  alpha := 1 / 4
  eta := (2 : Real) ^ (-(44 : Int))
  alpha_pos := by norm_num
  alpha_at_most_one := by norm_num
  card_A := by norm_num
  separately_freiman := by
    constructor <;> intro x <;> constructor
    all_goals intros; simp_all
  eta_value := rfl
  mostly_respected := by
    have he : respectedArrangementCount 8 ({(0, 0)} : Finset (Pair 2)) (fun _ => 0) =
        arrangementCount 8 ({(0, 0)} : Finset (Pair 2)) := by
      apply countWhere_congr
      intro R
      simp [DArrangement.IsRespected, IsAdditiveTuple]
    unfold MostlyRespectsEight
    rw [he]
    have hn : (0 : Real) ≤ arrangementCount 8 ({(0, 0)} : Finset (Pair 2)) := Nat.cast_nonneg _
    have heta : (0 : Real) ≤ (2 : Real) ^ (-(44 : Int)) := by positivity
    nlinarith only [hn, heta]

private def bad139Initial : Stage134Data 2 where
  q := 0
  m := 0
  P := modInterval 2 0 2
  H := Finset.univ
  a := fun _ => 0
  b := fun _ => 0

private def bad139Height : Stage135Data 2 := ⟨modInterval 2 0 1⟩
private def bad139Rows : Stage136Data 2 := ⟨modInterval 2 0 2, fun _ => ∅⟩
private def bad139Columns : Stage137Data 2 := ⟨0, modInterval 2 0 2, {(0, 0)}⟩
private def bad139Coefficients : Stage138Data 2 := ⟨fun _ => 0, fun _ => 0, {0}, {(0, 0)}⟩

private theorem bad139_height_carrier : bad139Height.Q.carrier = {0} := by
  ext x
  simp [bad139Height, modInterval, ModAP.carrier]

private theorem bad139_strong_zero : IsStrongHeight bad139Context 0 := by
  classical
  have hc : 1 ≤ section13C bad139Context 0 := by
    apply Nat.succ_le_iff.mpr
    exact countWhere_pos_of_witness
      (fun R : DArrangement 2 8 => R.IsIn bad139Context.A ∧ R.height = 0)
      ((fun _ => 0), (fun _ => 0), 0) (by
        simp [bad139Context, DArrangement.IsIn, DArrangement.x, DArrangement.y,
          DArrangement.height, IsAdditiveTuple])
  have he : section13G bad139Context 0 = section13C bad139Context 0 := by
    unfold section13G section13C respectedArrangementCountAtHeight arrangementCountAtHeight
    apply countWhere_congr
    intro R
    simp [bad139Context, DArrangement.IsRespected, IsAdditiveTuple]
  constructor
  · change (1 / 4 : Real) ^ 32 * 2 ^ 31 / 16 ≤ section13C bad139Context 0
    exact (by norm_num : (1 / 4 : Real) ^ 32 * 2 ^ 31 / 16 ≤ 1).trans (by exact_mod_cast hc)
  · unfold IsGoodHeight
    rw [he]
    change (1 - 2 * ((2 : Real) ^ (-(44 : Int)))) * section13C bad139Context 0 ≤ _
    have hn : (0 : Real) ≤ section13C bad139Context 0 := Nat.cast_nonneg _
    have heta : (0 : Real) ≤ (2 : Real) ^ (-(44 : Int)) := by positivity
    nlinarith only [hn, heta]

private theorem bad139_critical : criticalHeights bad139Context bad139Initial bad139Height = {0} := by
  ext x
  simp only [criticalHeights, Finset.mem_filter, Finset.mem_inter, bad139_height_carrier,
    bad139Initial, Finset.mem_univ, and_true, Finset.mem_singleton]
  constructor
  · exact And.left
  · rintro rfl
    exact ⟨rfl, bad139_strong_zero⟩

private theorem bad139_stage137 :
    IsStage137Data bad139Context bad139Initial bad139Height bad139Rows bad139Columns := by
  have hproper : (modInterval 2 0 2).IsProper := by
    unfold ModAP.IsProper
    rw [modInterval_zero_modulus_carrier, Finset.card_univ, ZMod.card]
    rfl
  constructor
  · refine ⟨by norm_num [bad139Columns, modInterval], hproper, Finset.Subset.refl _, ?_, ?_, ?_, ?_, ?_⟩
    · change (2 : Real) ^ ((2 : Real) ^ (-(100 : Int)) * (1 / 4) ^ 448) ≤ 2
      calc
        _ ≤ (2 : Real) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            have hp : (1 / 4 : Real) ^ (448 : Nat) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
            have hz : (2 : Real) ^ (-(100 : Int)) ≤ 1 := by norm_num
            exact mul_le_one₀ hz (by positivity) hp)
        _ = _ := Real.rpow_one _
    · rw [bad139_critical]
      intro p hp
      have he : p = (0, 0) := Finset.mem_singleton.mp hp
      subst p
      simp [bad139Columns, modInterval_zero_modulus_carrier, translateFinset, Finset.product]
    · rw [bad139_critical]
      norm_num [bad139Context, bad139Columns, modInterval]
    · norm_num [bad139Context, bad139Height, bad139Columns, modInterval]
    · intro h _
      refine ⟨0, 0, ?_⟩
      intros
      simp [bad139Context]
  · exact Finset.Subset.refl _

private theorem bad139_stage138 :
    IsStage138Data bad139Context bad139Initial bad139Height bad139Columns bad139Coefficients := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intros; simp [bad139Context, bad139Coefficients]
  · rw [bad139_critical]; exact Finset.Subset.refl _
  · constructor <;> intros <;> simp [bad139Coefficients]
  · ext p
    simp [bad139Coefficients, bad139Columns]
    aesop
  · simp only [bad139Context, bad139Height, bad139Columns, bad139Coefficients, modInterval,
      Finset.card_singleton, Nat.cast_ofNat, Nat.cast_one]
    have hp : (1 / 4 : Real) ^ (704 : Nat) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      _ ≤ (2 : Real) ^ (-(135 : Int)) * 1 * 1 * 2 := by gcongr
      _ ≤ _ := by norm_num

theorem lemma_13_9_missing_geometry_counterexample :
    ¬ lemma_13_9_without_preceding_geometry := by
  intro h
  obtain ⟨J, hJ⟩ := h 2 bad139Context bad139Initial bad139Height bad139Rows bad139Columns
    bad139Coefficients bad139_stage137 bad139_stage138
  have hl := stage139_height_card_lower bad139Context bad139Height bad139Columns bad139Coefficients J hJ
  rw [bad139_height_carrier, Finset.card_singleton] at hl
  have ht : (1 : Real) < (2 : Real) ^ ((2 : Real) ^ (-(284 : Int)) * (1 / 4) ^ 1408) :=
    Real.one_lt_rpow (by norm_num) (by positivity)
  simp only [bad139Columns, bad139Context, modInterval, Nat.cast_ofNat, Nat.cast_one] at hl
  exact (not_lt_of_ge hl) ht

end LeanProofs.GowersSzemeredi
