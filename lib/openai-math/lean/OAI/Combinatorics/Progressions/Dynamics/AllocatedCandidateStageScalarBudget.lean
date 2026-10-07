import OAI.Combinatorics.Progressions.Nilpotent.AllocatedKeptCommonCurrentGradeLocalNiltest

namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration

def allocatedCandidateStageResetInput (s m : ℕ) (v : ℝ) : ℝ :=
  v + (v + 2) ^ 4 + ((s : ℝ) + 1) + s * (v + 1) +
    s * (((m : ℝ) + 1) + m * (v + 1))

noncomputable def allocatedCandidateStageResetLog (s m : ℕ) (v : ℝ) : ℝ :=
  (allocatedCandidateStageResetInput s m v + allocatedFrozenCurrentGradeResetConstant s 1) ^
    allocatedFrozenCurrentGradeResetConstant s 1

noncomputable def allocatedCandidateStageLocalInput (s m : ℕ) (v : ℝ) : ℝ :=
  allocatedCandidateStageResetLog s m v + v ^ 2 + 2 * v + 2

noncomputable def allocatedCandidateStageSliceLog (s m : ℕ) (v : ℝ) : ℝ :=
  (allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ)) ^ (s + 401) +
    2 * (v + 2) ^ 9 + v + s + 4

attribute [local irreducible] allocatedFrozenCurrentGradeResetConstant
  allocatedCandidateStageResetLog allocatedCandidateStageLocalInput allocatedCandidateStageSliceLog

theorem allocatedCandidateStage_reset_lower (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    v + (v + 2) ^ 4 ≤ allocatedCandidateStageResetInput s m v := by
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hrest : 0 ≤ ((s : ℝ) + 1) + s * (v + 1) +
      s * (((m : ℝ) + 1) + m * (v + 1)) := by positivity
  unfold allocatedCandidateStageResetInput
  linarith only [hrest]

theorem allocatedCandidateStage_reset_bounds (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    v ≤ allocatedCandidateStageResetInput s m v ∧
    0 ≤ allocatedCandidateStageResetInput s m v := by
  have h := allocatedCandidateStage_reset_lower s m hv
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hpow : 0 ≤ (v + 2) ^ 4 := by positivity
  exact ⟨by linarith only [h, hpow], by linarith only [h, hpow, hv0]⟩

theorem allocatedCandidateStage_allowance (s m dtags dsampler : ℕ)
    {v budget : ℝ} (hv : 2 ≤ v) (htags : (dtags : ℝ) ≤ v)
    (hsampler : (dsampler : ℝ) ≤ v) (hbudget : budget ≤ v) :
    ((s : ℝ) + 1) * ((dtags : ℝ) + 1) ^ s * Real.exp budget *
      ((((m : ℝ) + 1) * ((dsampler : ℝ) + 1) ^ m) ^ s) ≤
        Real.exp (allocatedCandidateStageResetInput s m v + 2) := by
  have hv0 : 0 ≤ v := by linarith only [hv]
  have htagsExp : (dtags : ℝ) + 1 ≤ Real.exp (v + 1) := by
    linarith only [htags, Real.add_one_le_exp (v + 1)]
  have hsamplerExp : (dsampler : ℝ) + 1 ≤ Real.exp (v + 1) := by
    linarith only [hsampler, Real.add_one_le_exp (v + 1)]
  have hsExp : (s : ℝ) + 1 ≤ Real.exp ((s : ℝ) + 1) := by
    linarith only [Real.add_one_le_exp ((s : ℝ) + 1)]
  have hmExp : (m : ℝ) + 1 ≤ Real.exp ((m : ℝ) + 1) := by
    linarith only [Real.add_one_le_exp ((m : ℝ) + 1)]
  have htagsPow : ((dtags : ℝ) + 1) ^ s ≤ Real.exp ((s : ℝ) * (v + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) htagsExp s
  have hsamplerPow : ((dsampler : ℝ) + 1) ^ m ≤ Real.exp ((m : ℝ) * (v + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hsamplerExp m
  have hinner : ((m : ℝ) + 1) * ((dsampler : ℝ) + 1) ^ m ≤
      Real.exp (((m : ℝ) + 1) + m * (v + 1)) := by
    rw [Real.exp_add]
    exact mul_le_mul hmExp hsamplerPow (by positivity) (Real.exp_nonneg _)
  have hinnerPow : (((m : ℝ) + 1) * ((dsampler : ℝ) + 1) ^ m) ^ s ≤
      Real.exp ((s : ℝ) * (((m : ℝ) + 1) + m * (v + 1))) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hinner s
  calc
    _ ≤ Real.exp ((s : ℝ) + 1) * Real.exp ((s : ℝ) * (v + 1)) * Real.exp budget *
        Real.exp ((s : ℝ) * (((m : ℝ) + 1) + m * (v + 1))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hsExp htagsPow (by positivity) (Real.exp_nonneg _)) (Real.exp_nonneg _))
        hinnerPow (by positivity) (by positivity)
    _ = Real.exp (((s : ℝ) + 1) + s * (v + 1) + budget +
        s * (((m : ℝ) + 1) + m * (v + 1))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hpow : 0 ≤ (v + 2) ^ 4 := by positivity
      unfold allocatedCandidateStageResetInput
      linarith only [hbudget, hpow]

theorem allocatedCandidateStage_common_bound (s m : ℕ) {v budget : ℝ}
    (hv : 2 ≤ v) (hbudget : budget ≤ v) :
    Real.exp budget * Real.exp ((v + 2) ^ 4) ≤
      Real.exp (allocatedCandidateStageResetInput s m v) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr
    ((add_le_add hbudget le_rfl).trans (allocatedCandidateStage_reset_lower s m hv))

theorem allocatedCandidateStage_mapSlow_bound (s m : ℕ) {v qNative : ℝ}
    (hv : 2 ≤ v) (hqNative : qNative ≤ v) :
    Real.exp ((v + 2) ^ 3 + qNative) ≤
      Real.exp (allocatedCandidateStageResetInput s m v + 2) := by
  have hpow : (v + 2) ^ 3 ≤ (v + 2) ^ 4 :=
    pow_le_pow_right₀ (by linarith only [hv]) (by norm_num)
  have h := allocatedCandidateStage_reset_lower s m hv
  exact Real.exp_le_exp.mpr (by linarith only [hpow, hqNative, h])

theorem allocatedCandidateStage_resetLog_nonneg (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    0 ≤ allocatedCandidateStageResetLog s m v := by
  unfold allocatedCandidateStageResetLog
  exact pow_nonneg (add_nonneg (allocatedCandidateStage_reset_bounds s m hv).2
    (Nat.cast_nonneg _)) _

theorem allocatedCandidateStage_local_bounds (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    1 ≤ allocatedCandidateStageLocalInput s m v ∧
    v ≤ allocatedCandidateStageLocalInput s m v ∧
    allocatedCandidateStageResetLog s m v ≤ allocatedCandidateStageLocalInput s m v := by
  have hR := allocatedCandidateStage_resetLog_nonneg s m hv
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  unfold allocatedCandidateStageLocalInput
  exact ⟨by linarith only [hR, hv, hv2], by linarith only [hR, hv, hv2],
    by linarith only [hv, hv2]⟩

theorem allocatedCandidateStage_localSize_bound (s m d Hθ : ℕ) {v : ℝ}
    (_hv : 2 ≤ v) (hd : (d : ℝ) ≤ v) (hθ : (Hθ : ℝ) ≤ Real.exp v) :
    (d : ℝ) * Hθ * Real.exp (allocatedCandidateStageResetLog s m v) ≤
      Real.exp (allocatedCandidateStageLocalInput s m v) := by
  have hdExp : (d : ℝ) ≤ Real.exp v := by
    linarith only [hd, Real.add_one_le_exp v]
  calc
    _ ≤ Real.exp v * Real.exp v * Real.exp (allocatedCandidateStageResetLog s m v) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hdExp hθ (Nat.cast_nonneg Hθ) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (v + v + allocatedCandidateStageResetLog s m v) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold allocatedCandidateStageLocalInput
      nlinarith only [sq_nonneg v]

theorem allocatedCandidateStage_localDen_bound (s m d Hθ : ℕ) {v : ℝ}
    (hv : 2 ≤ v) (hd : (d : ℝ) ≤ v) (hθ : (Hθ : ℝ) ≤ Real.exp v) :
    (Hθ : ℝ) ^ d * Real.exp (allocatedCandidateStageResetLog s m v) ≤
      Real.exp (allocatedCandidateStageLocalInput s m v) := by
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hpow : (Hθ : ℝ) ^ d ≤ Real.exp ((d : ℝ) * v) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg Hθ) hθ d
  calc
    _ ≤ Real.exp ((d : ℝ) * v) * Real.exp (allocatedCandidateStageResetLog s m v) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = Real.exp ((d : ℝ) * v + allocatedCandidateStageResetLog s m v) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hdv := mul_le_mul_of_nonneg_right hd hv0
      unfold allocatedCandidateStageLocalInput
      nlinarith only [hdv, hv]

theorem allocatedCandidateStage_localCost_le_slice (s m r : ℕ) {v : ℝ}
    (hv : 2 ≤ v) (hrs : r ≤ s) :
    (allocatedCandidateStageLocalInput s m v + (r + 401 : ℕ)) ^ (r + 401) ≤
      allocatedCandidateStageSliceLog s m v := by
  have hL := (allocatedCandidateStage_local_bounds s m hv).1
  have hL0 : 0 ≤ allocatedCandidateStageLocalInput s m v := le_trans (by norm_num) hL
  have hshift : allocatedCandidateStageLocalInput s m v + (r + 401 : ℕ) ≤
      allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ) :=
    add_le_add le_rfl (Nat.cast_le.mpr (Nat.add_le_add_right hrs 401))
  have hbase : 1 ≤ allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ) := by
    linarith only [hL, Nat.cast_nonneg (α := ℝ) (s + 401)]
  have hpower :
      (allocatedCandidateStageLocalInput s m v + (r + 401 : ℕ)) ^ (r + 401) ≤
      (allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ)) ^ (s + 401) := by
    exact (pow_le_pow_left₀ (by positivity) hshift (r + 401)).trans
      (pow_le_pow_right₀ hbase (Nat.add_le_add_right hrs 401))
  have hrest : 0 ≤ 2 * (v + 2) ^ 9 + v + s + 4 := by positivity
  unfold allocatedCandidateStageSliceLog
  linarith only [hpower, hrest]

private theorem stageSlice_addition_bounds (s : ℕ) {v P R : ℝ}
    (hv : 2 ≤ v) (hP : 0 ≤ P) (hRP : R ≤ P) :
    0 ≤ P + 2 * (v + 2) ^ 9 + v + s + 4 ∧
    R ≤ P + 2 * (v + 2) ^ 9 + v + s + 4 ∧
    v + s + 1 ≤ P + 2 * (v + 2) ^ 9 + v + s + 4 ∧
    2 * (v + 2) ^ 9 < P + 2 * (v + 2) ^ 9 + v + s + 4 := by
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hvpow : 0 ≤ 2 * (v + 2) ^ 9 := by positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  exact ⟨by linarith only [hP, hvpow, hv, hs0],
    by linarith only [hRP, hvpow, hv, hs0],
    by linarith only [hP, hvpow],
    by linarith only [hP, hv, hs0]⟩

theorem allocatedCandidateStage_slice_bounds (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    0 ≤ allocatedCandidateStageSliceLog s m v ∧
    allocatedCandidateStageResetLog s m v ≤ allocatedCandidateStageSliceLog s m v ∧
    v + s + 1 ≤ allocatedCandidateStageSliceLog s m v ∧
    2 * (v + 2) ^ 9 < allocatedCandidateStageSliceLog s m v := by
  have hL := allocatedCandidateStage_local_bounds s m hv
  have hL0 : 0 ≤ allocatedCandidateStageLocalInput s m v := le_trans (by norm_num) hL.1
  have hbase : 1 ≤ allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ) := by
    linarith only [hL.1, Nat.cast_nonneg (α := ℝ) (s + 401)]
  have hLPow : allocatedCandidateStageLocalInput s m v ≤
      (allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ)) ^ (s + 401) := by
    calc
      _ ≤ allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg (s + 401))
      _ = (allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ)) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hbase (by omega : 1 ≤ s + 401)
  unfold allocatedCandidateStageSliceLog
  exact stageSlice_addition_bounds s hv (hL0.trans hLPow) (hL.2.2.trans hLPow)

theorem exists_allocatedCandidateStageSliceLog_budget (s m Cbase : ℕ) :
    ∃ Cslice : ℕ, 2 ≤ Cslice ∧ ∀ b : ℝ, 0 ≤ b →
      allocatedCandidateStageSliceLog s m ((b + Cbase) ^ Cbase) ≤ (b + Cslice) ^ Cslice := by
  let V : Polynomial ℕ := (Polynomial.X + Polynomial.C Cbase) ^ Cbase
  let P : Polynomial ℕ := V + (V + 2) ^ 4 + Polynomial.C (s + 1) +
    Polynomial.C s * (V + 1) + Polynomial.C s *
      (Polynomial.C (m + 1) + Polynomial.C m * (V + 1))
  let Creset := allocatedFrozenCurrentGradeResetConstant s 1
  let R : Polynomial ℕ := (P + Polynomial.C Creset) ^ Creset
  let L : Polynomial ℕ := R + V ^ 2 + 2 * V + 2
  let Q : Polynomial ℕ := (L + Polynomial.C (s + 401)) ^ (s + 401) +
    2 * (V + 2) ^ 9 + V + Polynomial.C s + 4
  obtain ⟨Cslice, hCslice, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨Cslice, hCslice, ?_⟩
  intro b hb
  simpa [Q, L, R, P, V, Creset, allocatedCandidateStageSliceLog,
    allocatedCandidateStageLocalInput, allocatedCandidateStageResetLog,
    allocatedCandidateStageResetInput, Polynomial.eval₂_pow, Nat.cast_add]
    using hbound b hb

end Erdos3.VectorPolynomial

end

end OAI
