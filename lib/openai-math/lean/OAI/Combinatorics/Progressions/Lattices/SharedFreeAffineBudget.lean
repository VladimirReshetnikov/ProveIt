import OAI.Combinatorics.Progressions.Dynamics.SharedFreeRecoveryBudget
import OAI.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
import OAI.Combinatorics.Progressions.Probability.RoundedModelDensityBudget

namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

noncomputable def affineRecoveryLogLoss (P : ℝ) (n : ℕ) : ℝ :=
  quarticBogolyubovProgressionConstant * (roundedModelLogBudget P n + 1) ^ 8 +
    (P + 13 * n) + 16 * ((n : ℝ) + 3)

theorem exp_neg_affineRecoveryLogLoss_card_le (P : ℝ) (n a b : ℕ)
    (h : Real.exp (-(quarticBogolyubovProgressionConstant *
        (roundedModelLogBudget P n + 1) ^ 8)) *
      ((2 ^ 4 : ℝ)⁻¹ * (Real.exp (P + 13 * n))⁻¹ * a) ≤
        16 ^ (n + 2) * (b : ℝ)) :
    Real.exp (-affineRecoveryLogLoss P n) * a ≤ (b : ℝ) := by
  let C := quarticBogolyubovProgressionConstant * (roundedModelLogBudget P n + 1) ^ 8
  let E := P + 13 * n
  let L := 16 * ((n : ℝ) + 3)
  have hmain : Real.exp (-(C + E)) * a ≤ (16 : ℝ) ^ (n + 3) * b := by
    calc
      _ = 16 * (Real.exp (-C) * ((2 ^ 4 : ℝ)⁻¹ * (Real.exp E)⁻¹ * a)) := by
        simp only [neg_add, Real.exp_add, Real.exp_neg]
        norm_num
        ring
      _ ≤ 16 * (16 ^ (n + 2) * (b : ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by rw [show n + 3 = n + 2 + 1 by omega, pow_succ]; ring
  have h16 : (16 : ℝ) ^ (n + 3) ≤ Real.exp L := by
    calc
      _ ≤ (Real.exp 16) ^ (n + 3) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (16 : ℝ)]) _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [L]
        push_cast
        ring
  calc
    _ = Real.exp (-L) * (Real.exp (-(C + E)) * a) := by
      change Real.exp (-(C + E + L)) * a = _
      rw [show -(C + E + L) = -L + -(C + E) by ring, Real.exp_add, mul_assoc]
    _ ≤ Real.exp (-L) * ((16 : ℝ) ^ (n + 3) * b) :=
      mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
    _ ≤ Real.exp (-L) * (Real.exp L * b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h16 (Nat.cast_nonneg _))
        (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

noncomputable def properAffineRankBound (P : ℝ) (n : ℕ) : ℝ :=
  2 + quarticBogolyubovConstant * (roundedModelLogBudget P n + 1) ^ 4

noncomputable def properAffineVolumeLog (P : ℝ) (n : ℕ) : ℝ :=
  2 + 16 * (44 + 6 * max P 0 + 94 * n)

noncomputable def properAffineScaleLog (P : ℝ) (n : ℕ) : ℝ :=
  2 * properAffineRankBound P n + properAffineVolumeLog P n + affineRecoveryLogLoss P n + 2

noncomputable def properAffineRecoveryLogLoss (P : ℝ) (n : ℕ) : ℝ :=
  affineRecoveryLogLoss P n + (4 + properAffineScaleLog P n) * properAffineRankBound P n

theorem affineBoxScale_le_exp {r V A B : ℕ} {R D S : ℝ}
    (hB : 0 < B) (hR : 0 ≤ R) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hr : (r : ℝ) ≤ R) (hV : (V : ℝ) ≤ Real.exp D * A)
    (hdense : Real.exp (-S) * A ≤ (B : ℝ)) :
    ((2 ^ r * V / B + 1 : ℕ) : ℝ) ≤ Real.exp (2 * R + D + S + 2) := by
  have hquot : ((2 ^ r * V / B + 1 : ℕ) : ℝ) * B ≤ (2 : ℝ) ^ r * V + B := by
    have h : (2 ^ r * V / B + 1) * B ≤ 2 ^ r * V + B := by
      calc
        _ = (2 ^ r * V / B) * B + B := by ring
        _ ≤ _ := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    exact_mod_cast h
  have htwo : (2 : ℝ) ^ r ≤ Real.exp (2 * R) := by
    calc
      _ ≤ (Real.exp 2) ^ r := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) _
      _ = Real.exp (2 * (r : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hr])
  have hA : (A : ℝ) ≤ Real.exp S * B := by
    calc
      _ = Real.exp S * (Real.exp (-S) * A) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hdense (Real.exp_pos _).le
  have hprod : (2 : ℝ) ^ r * V ≤ Real.exp (2 * R + D + S) * B := by
    calc
      _ ≤ Real.exp (2 * R) * (Real.exp D * A) := by gcongr
      _ ≤ Real.exp (2 * R) * (Real.exp D * (Real.exp S * B)) := by gcongr
      _ = _ := by simp only [Real.exp_add]; ring
  have hplus : Real.exp (2 * R + D + S) + 1 ≤ Real.exp (2 * R + D + S + 2) := by
    have hone : 1 ≤ Real.exp (2 * R + D + S) := Real.one_le_exp_iff.mpr (by linarith)
    calc
      _ ≤ 2 * Real.exp (2 * R + D + S) := by linarith only [hone]
      _ ≤ Real.exp 2 * Real.exp (2 * R + D + S) := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (mul_le_mul_iff_left₀ (by exact_mod_cast hB : (0 : ℝ) < B)).mp
  calc
    _ ≤ (2 : ℝ) ^ r * V + B := hquot
    _ ≤ Real.exp (2 * R + D + S) * B + B := add_le_add hprod (le_refl (B : ℝ))
    _ = (Real.exp (2 * R + D + S) + 1) * B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hplus (Nat.cast_nonneg _)

theorem affineBoxCellCount_le_exp {r k : ℕ} {R T : ℝ}
    (hT : 0 ≤ T) (hr : (r : ℝ) ≤ R) (hk : (k : ℝ) ≤ Real.exp T) :
    ((4 * k) ^ r : ℕ) ≤ Real.exp ((4 + T) * R) := by
  have hbase : (4 : ℝ) * k ≤ Real.exp (4 + T) := by
    calc
      _ ≤ Real.exp 4 * Real.exp T := by
        gcongr
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = _ := (Real.exp_add _ _).symm
  calc
    (((4 * k) ^ r : ℕ) : ℝ) = ((4 : ℝ) * k) ^ r := by push_cast; rfl
    _ ≤ (Real.exp (4 + T)) ^ r := pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp ((4 + T) * (r : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr (by linarith))

theorem properAffineVolume_bound (P : ℝ) (n : ℕ) :
    2 * ((2 ^ 14 : ℝ) * (Real.exp (P + 13 * n)) ^ 6 * 16 ^ (n + 1)) ^ 16 ≤
      Real.exp (properAffineVolumeLog P n) := by
  calc
    _ ≤ Real.exp 2 * (Real.exp (44 + 6 * max P 0 + 94 * n)) ^ 16 := by
      gcongr
      · linarith [Real.add_one_le_exp (2 : ℝ)]
      · exact roundedModelScale_le_exp P n
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1

theorem properAffineSelection_bounds {P : ℝ} (hP : 0 ≤ P) (n r V A B C : ℕ)
    (hB : 0 < B) (hr : (r : ℝ) ≤ properAffineRankBound P n)
    (hV : (V : ℝ) ≤
      2 * ((2 ^ 14 : ℝ) * (Real.exp (P + 13 * n)) ^ 6 * 16 ^ (n + 1)) ^ 16 * A)
    (hdense : Real.exp (-affineRecoveryLogLoss P n) * A ≤ (B : ℝ))
    (hcell : B ≤ (4 * (2 ^ r * V / B + 1)) ^ r * C) :
    ((2 ^ r * V / B + 1 : ℕ) : ℝ) ≤ Real.exp (properAffineScaleLog P n) ∧
      Real.exp (-properAffineRecoveryLogLoss P n) * A ≤ (C : ℝ) := by
  have hR : 0 ≤ properAffineRankBound P n := by
    have hc := quarticBogolyubovConstant_pos.le
    unfold properAffineRankBound
    positivity
  have hD : 0 ≤ properAffineVolumeLog P n := by unfold properAffineVolumeLog; positivity
  have hS : 0 ≤ affineRecoveryLogLoss P n := by
    have hc := quarticBogolyubovProgressionConstant_pos.le
    unfold affineRecoveryLogLoss
    positivity
  have hT : 0 ≤ properAffineScaleLog P n := by unfold properAffineScaleLog; positivity
  have hV' : (V : ℝ) ≤ Real.exp (properAffineVolumeLog P n) * A :=
    hV.trans (mul_le_mul_of_nonneg_right (properAffineVolume_bound P n) (Nat.cast_nonneg _))
  have hk := affineBoxScale_le_exp hB hR hD hS hr hV' hdense
  have hcount := affineBoxCellCount_le_exp hT hr hk
  refine ⟨hk, ?_⟩
  have hcellR : (B : ℝ) ≤ ((4 * (2 ^ r * V / B + 1)) ^ r : ℕ) * (C : ℝ) := by
    exact_mod_cast hcell
  have hBC : (B : ℝ) ≤ Real.exp ((4 + properAffineScaleLog P n) * properAffineRankBound P n) * C :=
    hcellR.trans (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _))
  let T := (4 + properAffineScaleLog P n) * properAffineRankBound P n
  calc
    _ = Real.exp (-T) * (Real.exp (-affineRecoveryLogLoss P n) * A) := by
      unfold properAffineRecoveryLogLoss
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      dsimp [T]
      ring
    _ ≤ Real.exp (-T) * (Real.exp T * C) :=
      mul_le_mul_of_nonneg_left (hdense.trans hBC) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

theorem exists_quadratic_affine_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let P := 1024 * (p + 1)
      P + properAffineRecoveryLogLoss P 1 ≤ (p + C) ^ C ∧
        properAffineRankBound P 1 ≤ (p + C) ^ C ∧ P ≤ (p + C) ^ C := by
  let c := ⌈max quarticBogolyubovProgressionConstant quarticBogolyubovConstant⌉₊
  have hc₀ : quarticBogolyubovProgressionConstant ≤ (c : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hc₁ : quarticBogolyubovConstant ≤ (c : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  let PB : Polynomial ℕ := 1024 * (Polynomial.X + 1)
  let PZ : Polynomial ℕ := 736 + 96 * PB + 1504
  let PR : Polynomial ℕ := 2 + Polynomial.C c * (PZ + 1) ^ 4
  let PA : Polynomial ℕ := Polynomial.C c * (PZ + 1) ^ 8 + (PB + 13) + 64
  let PV : Polynomial ℕ := 2 + 16 * (44 + 6 * PB + 94)
  let PT : Polynomial ℕ := 2 * PR + PV + PA + 2
  let PL : Polynomial ℕ := PA + (4 + PT) * PR
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (PB + PL + PR)
  refine ⟨C, hC, ?_⟩
  intro p hp B
  let Z := 736 + 96 * B + 1504
  let R := 2 + (c : ℝ) * (Z + 1) ^ 4
  let A := (c : ℝ) * (Z + 1) ^ 8 + (B + 13) + 64
  let V := 2 + 16 * (44 + 6 * B + 94)
  let T := 2 * R + V + A + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hz : roundedModelLogBudget B 1 = Z := by
    simp [roundedModelLogBudget, max_eq_left hB, Z]
  have hrank : properAffineRankBound B 1 ≤ R := by
    unfold properAffineRankBound
    rw [hz]
    dsimp [R]
    gcongr
  have hloss : affineRecoveryLogLoss B 1 ≤ A := by
    unfold affineRecoveryLogLoss
    rw [hz]
    dsimp [A]
    norm_num
    gcongr
  have hvolume : properAffineVolumeLog B 1 = V := by
    simp [properAffineVolumeLog, max_eq_left hB, V]
  have hscale : properAffineScaleLog B 1 ≤ T := by
    unfold properAffineScaleLog
    rw [hvolume]
    dsimp [T]
    linarith
  have hrank0 : 0 ≤ properAffineRankBound B 1 := by
    have hc := quarticBogolyubovConstant_pos.le
    unfold properAffineRankBound
    positivity
  have hproper : properAffineRecoveryLogLoss B 1 ≤ A + (4 + T) * R := by
    unfold properAffineRecoveryLogLoss
    exact add_le_add hloss (mul_le_mul (by linarith) hrank hrank0 (by linarith))
  have htotal : B + (A + (4 + T) * R) + R ≤ (p + C) ^ C := by
    simpa [PB, PL, PR, PA, PZ, PV, PT, B, Z, R, A, V, T, Polynomial.eval₂_pow]
      using hbound p hp
  have hproper0 : 0 ≤ A + (4 + T) * R := by positivity
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

theorem exists_sharedFreeProperAffineSelection_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
      properAffineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
      properAffineScaleLog ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
      properAffineRankBound ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C := by
  let c := ⌈max quarticBogolyubovProgressionConstant quarticBogolyubovConstant⌉₊
  have hc₀ : quarticBogolyubovProgressionConstant ≤ (c : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hc₁ : quarticBogolyubovConstant ≤ (c : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  let PB : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X
  let PD : Polynomial ℕ := 4 * Polynomial.C s * Polynomial.X
  let PZ : Polynomial ℕ := 736 + 96 * PB + 1504 * PD
  let PR : Polynomial ℕ := 2 + Polynomial.C c * (PZ + 1) ^ 4
  let PA : Polynomial ℕ := Polynomial.C c * (PZ + 1) ^ 8 + (PB + 13 * PD) + 16 * (PD + 3)
  let PV : Polynomial ℕ := 2 + 16 * (44 + 6 * PB + 94 * PD)
  let PT : Polynomial ℕ := 2 * PR + PV + PA + 2
  let PL : Polynomial ℕ := PA + (4 + PT) * PR
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (PL + PT + PR)
  refine ⟨C, hC, ?_⟩
  intro p hp n hn
  let B := (p + 2) ^ 3 + 2 * p
  let D := 4 * (s : ℝ) * p
  let Z := 736 + 96 * B + 1504 * D
  let R := 2 + (c : ℝ) * (Z + 1) ^ 4
  let A := (c : ℝ) * (Z + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3)
  let V := 2 + 16 * (44 + 6 * B + 94 * D)
  let T := 2 * R + V + A + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hz : roundedModelLogBudget B n ≤ Z := by
    unfold roundedModelLogBudget
    rw [max_eq_left hB]
    dsimp [Z]
    gcongr
  have hz0 : 0 ≤ roundedModelLogBudget B n + 1 := by
    linarith [roundedModelLogBudget_nonneg B n]
  have hrank : properAffineRankBound B n ≤ R := by
    unfold properAffineRankBound
    dsimp [R]
    gcongr
  have hloss : affineRecoveryLogLoss B n ≤ A := by
    unfold affineRecoveryLogLoss
    dsimp [A]
    gcongr
  have hvolume : properAffineVolumeLog B n ≤ V := by
    unfold properAffineVolumeLog
    rw [max_eq_left hB]
    dsimp [V]
    gcongr
  have hscale : properAffineScaleLog B n ≤ T := by
    unfold properAffineScaleLog
    dsimp [T]
    linarith only [hrank, hloss, hvolume]
  have hrank0 : 0 ≤ properAffineRankBound B n := by
    have hc := quarticBogolyubovConstant_pos.le
    unfold properAffineRankBound
    positivity
  have hloss0 : 0 ≤ affineRecoveryLogLoss B n := by
    have hc := quarticBogolyubovProgressionConstant_pos.le
    unfold affineRecoveryLogLoss
    positivity
  have hscale0 : 0 ≤ properAffineScaleLog B n := by
    unfold properAffineScaleLog properAffineVolumeLog
    positivity
  have hproper : properAffineRecoveryLogLoss B n ≤ A + (4 + T) * R := by
    unfold properAffineRecoveryLogLoss
    exact add_le_add hloss (mul_le_mul (by linarith only [hscale]) hrank hrank0
      (by linarith only [hT]))
  have heval : (PL + PT + PR).eval₂ (Nat.castRingHom ℝ) p = A + (4 + T) * R + T + R := by
    simp [PL, PT, PV, PA, PR, PZ, PD, PB, B, D, Z, R, A, V, T, Polynomial.eval₂_pow]
  have htotal := hbound p hp
  rw [heval] at htotal
  have hproper0 : 0 ≤ A + (4 + T) * R := by positivity
  exact ⟨hproper.trans (by linarith only [htotal, hT, hR]),
    hscale.trans (by linarith only [htotal, hproper0, hR]),
    hrank.trans (by linarith only [htotal, hproper0, hT])⟩

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

theorem exists_sharedFreeAffineSelection_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
      affineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
      2 + quarticBogolyubovConstant *
        (roundedModelLogBudget ((p + 2) ^ 3 + 2 * p) n + 1) ^ 4 ≤ (p + C) ^ C := by
  let C₀ := ⌈max quarticBogolyubovProgressionConstant quarticBogolyubovConstant⌉₊
  have hC₀ : quarticBogolyubovProgressionConstant ≤ (C₀ : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hC₁ : quarticBogolyubovConstant ≤ (C₀ : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  let PB : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X
  let PD : Polynomial ℕ := 4 * Polynomial.C s * Polynomial.X
  let PZ : Polynomial ℕ := 736 + 96 * PB + 1504 * PD
  let T : Polynomial ℕ := Polynomial.C C₀ * (PZ + 1) ^ 8 +
    (PB + 13 * PD) + 16 * (PD + 3) + (2 + Polynomial.C C₀ * (PZ + 1) ^ 4)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro p hp n hn
  let B := (p + 2) ^ 3 + 2 * p
  let D := 4 * (s : ℝ) * p
  let U := 736 + 96 * B + 1504 * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hz : roundedModelLogBudget B n ≤ U := by
    unfold roundedModelLogBudget
    rw [max_eq_left hB]
    dsimp [U]
    gcongr
  have hz0 : 0 ≤ roundedModelLogBudget B n + 1 := by
    linarith [roundedModelLogBudget_nonneg B n]
  have hcost : affineRecoveryLogLoss B n ≤
      (C₀ : ℝ) * (U + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3) := by
    unfold affineRecoveryLogLoss
    gcongr
  have hrank : 2 + quarticBogolyubovConstant * (roundedModelLogBudget B n + 1) ^ 4 ≤
      2 + (C₀ : ℝ) * (U + 1) ^ 4 := by gcongr
  have heval : T.eval₂ (Nat.castRingHom ℝ) p =
      (C₀ : ℝ) * (U + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3) +
        (2 + (C₀ : ℝ) * (U + 1) ^ 4) := by
    simp [T, PZ, PD, PB, B, D, U, Polynomial.eval₂_pow]
  have htotal := hbound p hp
  rw [heval] at htotal
  have hcost0 : 0 ≤ (C₀ : ℝ) * (U + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3) := by
    positivity
  have hrank0 : 0 ≤ 2 + (C₀ : ℝ) * (U + 1) ^ 4 := by positivity
  constructor <;> linarith

theorem exists_sharedFreeAffineUniform_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
        sharedFreeRecoveryThreshold s q p ≤ (p + C) ^ C ∧
        affineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
        2 + quarticBogolyubovConstant *
          (roundedModelLogBudget ((p + 2) ^ 3 + 2 * p) n + 1) ^ 4 ≤ (p + C) ^ C := by
  obtain ⟨C₁, hC₁, hthreshold⟩ := exists_sharedFreeRecoveryThreshold_bound s
  obtain ⟨C₂, hC₂, hselection⟩ := exists_sharedFreeAffineSelection_bound s
  let C := C₁ + C₂
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp n hn
  have hshift (c : ℕ) (hc : c ≤ C) : (p + c) ^ c ≤ (p + C) ^ C := by
    have hcR : (c : ℝ) ≤ C := by exact_mod_cast hc
    have hCR : (2 : ℝ) ≤ C := by exact_mod_cast hC
    exact (pow_le_pow_left₀ (by positivity) (by linarith : p + c ≤ p + C) c).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + C) hc)
  have h₁ := hshift C₁ (by dsimp [C]; omega)
  have h₂ := hshift C₂ (by dsimp [C]; omega)
  have hs := hselection p hp n hn
  exact ⟨(hthreshold q p hq hqp hp).trans h₁, hs.1.trans h₂, hs.2.trans h₂⟩

noncomputable def sharedFreeAffineConstant (s : ℕ) : ℕ :=
  (exists_sharedFreeAffineUniform_bound s).choose +
    (exists_sharedFreeProperAffineSelection_bound s).choose

theorem sharedFreeAffineConstant_two_le (s : ℕ) : 2 ≤ sharedFreeAffineConstant s := by
  have h := (exists_sharedFreeAffineUniform_bound s).choose_spec.1
  unfold sharedFreeAffineConstant
  omega

theorem sharedFreeAffineConstant_shift_bound (s : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (c : ℕ) (hc : c ≤ sharedFreeAffineConstant s) :
    (p + c) ^ c ≤ (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s := by
  have hcR : (c : ℝ) ≤ sharedFreeAffineConstant s := by exact_mod_cast hc
  have hCR : (2 : ℝ) ≤ sharedFreeAffineConstant s := by
    exact_mod_cast sharedFreeAffineConstant_two_le s
  exact (pow_le_pow_left₀ (by positivity)
    (by linarith : p + c ≤ p + sharedFreeAffineConstant s) c).trans
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + sharedFreeAffineConstant s) hc)

theorem sharedFreeAffineConstant_spec (s : ℕ) :
    2 ≤ sharedFreeAffineConstant s ∧
      ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
        ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
          sharedFreeRecoveryThreshold s q p ≤ (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
          affineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤
            (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
          2 + quarticBogolyubovConstant *
            (roundedModelLogBudget ((p + 2) ^ 3 + 2 * p) n + 1) ^ 4 ≤
              (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s := by
  refine ⟨sharedFreeAffineConstant_two_le s, ?_⟩
  intro q p hq hqp hp n hn
  have h := (exists_sharedFreeAffineUniform_bound s).choose_spec.2 q p hq hqp hp n hn
  have hb := sharedFreeAffineConstant_shift_bound s hp
    (exists_sharedFreeAffineUniform_bound s).choose (by unfold sharedFreeAffineConstant; omega)
  exact ⟨h.1.trans hb, h.2.1.trans hb, h.2.2.trans hb⟩

theorem sharedFreeAffineConstant_proper_spec (s : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (n : ℕ) (hn : (n : ℝ) ≤ 4 * (s : ℝ) * p) :
    properAffineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
    properAffineScaleLog ((p + 2) ^ 3 + 2 * p) n ≤
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
    properAffineRankBound ((p + 2) ^ 3 + 2 * p) n ≤
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s := by
  have h := (exists_sharedFreeProperAffineSelection_bound s).choose_spec.2 p hp n hn
  have hb := sharedFreeAffineConstant_shift_bound s hp
    (exists_sharedFreeProperAffineSelection_bound s).choose (by unfold sharedFreeAffineConstant; omega)
  exact ⟨h.1.trans hb, h.2.1.trans hb, h.2.2.trans hb⟩

theorem sharedFreeRecoveryThreshold_coefficient_bounds (s : ℕ) {q p : ℝ}
    (hq : 0 ≤ q) (hp : 0 ≤ p) :
    let A := sharedFreeEquationInputBudget s q p
    let z := 8 * sharedRefinementInputBudget s p + 1
    (A + 2) ^ 4 ≤ sharedFreeRecoveryThreshold s q p ∧
      2 * (Real.exp ((A + 2) ^ 3) *
        (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) ≤
          Real.exp (sharedFreeRecoveryThreshold s q p) := by
  intro A z
  have hb := sharedFreeEquationInputBudget_bounds s hq hp
  have hA : 0 ≤ A := hb.1
  have hz : 0 ≤ z := by
    have hi := (sharedRefinementInputBudget_bounds s hp).2.2.1
    dsimp [z]
    linarith
  have hbudget : z + ((z + 2) ^ 3 + (z + 2) ^ 36) ≤ A := hb.2.2.2
  have hT : (A + 2) ^ 5 ≤ sharedFreeRecoveryThreshold s q p := le_max_right _ _
  refine ⟨(pow_le_pow_right₀ (by linarith : 1 ≤ A + 2) (by decide : 4 ≤ 5)).trans hT, ?_⟩
  have hzA : z ≤ A := by
    have h3 : 0 ≤ (z + 2) ^ 3 := by positivity
    have h36 : 0 ≤ (z + 2) ^ 36 := by positivity
    linarith
  have h18 : (z + 2) ^ 18 ≤ (z + 2) ^ 36 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hwA : (z + 2) ^ 3 + (z + 2) ^ 18 + z ≤ A := by linarith
  have hsum : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤
      2 * Real.exp A := by
    linarith [Real.exp_le_exp.mpr hzA, Real.exp_le_exp.mpr hwA]
  have hpoly : (A + 2) ^ 3 + A + 4 ≤ (A + 2) ^ 5 := by
    have hh : 0 ≤ A ^ 5 + 10 * A ^ 4 + 39 * A ^ 3 + 74 * A ^ 2 + 67 * A + 20 := by
      positivity
    nlinarith
  calc
    _ ≤ 2 * (Real.exp ((A + 2) ^ 3) * (2 * Real.exp A)) := by gcongr
    _ = 4 * Real.exp ((A + 2) ^ 3 + A) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp 4 * Real.exp ((A + 2) ^ 3 + A) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = Real.exp ((A + 2) ^ 3 + A + 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((A + 2) ^ 5) := Real.exp_le_exp.mpr hpoly
    _ ≤ _ := Real.exp_le_exp.mpr hT

end Erdos3

end

end OAI
