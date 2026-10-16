import GowersSzemeredi.Proofs16ClassStepDegrees
import GowersSzemeredi.Proofs16ClassStepBoundsFejer

/-! **The class-step degrees under the Fejér θ₁ and the tight radius**
(Notes L.16d).

The Fejér instance of `Proofs16ClassStepDegrees`, generated from it by a
script with a guard that no printed parameter survives. Given a uniform class
of dimension `k ≥ 1` at one degree `D`, and the family Lemma 16.6 at
dimension `k` with constants `K, p ≤ V′`, the relations covered by Fejér step
pieces (`StepPieceFejer`) form a uniform class of dimension `k+1` at base
`V′`, with degrees
* `fejerStepCountDeg k D`, `fejerStepExpDeg k D`, `fejerStepThrDeg k D`.

These are the corpus's degrees with `P = fejerStepP k = 64·F` in place of
`stepP k = 2^(2^(k+5)+6)` and `T = fejerStepT k = 22·F + 105` in place of
`stepT k = 2^(2^(k+6))`, where `F = fejerProductExponent k ≤ 2^(5k+14)`.
So every degree is `D · 2^(O(k))` rather than `D · 2^(2^(O(k)))`.

The six inputs are `Proofs16ClassStepBoundsFejer`. The generic lemmas
(`level_base_le`, `step_w_facts`, `inv_scale_le`, `classVertexNum_succ_le`,
`PowerUniformClass.weaken`) are reused from `Proofs16ClassStepDegrees`.

* `powerUniformClass_succ_fejer`: **the Fejér step of route (II)**. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The degrees -/

def fejerStepY1 (k : Nat) : Nat := 2 * fejerStepP k + k + 9
def fejerStepQrDeg (k D : Nat) : Nat := 2 ^ k * (D * fejerStepY1 k)
def fejerStepSDeg (k D : Nat) : Nat := fejerStepQrDeg k D + (fejerStepP k + 2) + 7
def fejerStepPbDeg (k D : Nat) : Nat := D * (fejerStepSDeg k D + 2 * fejerStepP k + 8)
def fejerStepEbDeg (k D : Nat) : Nat := D * (2 * fejerStepP k + 9)
def fejerStepErDeg (k D : Nat) : Nat := (4 + D * fejerStepY1 k) * 2 ^ k
def fejerStepBqDeg (k D : Nat) : Nat := 4 + (fejerStepEbDeg k D + 1) * 2 ^ (k + 2)
def fejerStepLDeg (k D : Nat) : Nat := fejerStepBqDeg k D + (fejerStepErDeg k D + fejerStepEbDeg k D)
def fejerStepZDeg (k D : Nat) : Nat := fejerStepT k + fejerStepEbDeg k D + 4

/-- The count degree of the next class. -/
def fejerStepCountDeg (k D : Nat) : Nat :=
  (fejerStepP k + 2) + (2 * fejerStepSDeg k D + fejerStepPbDeg k D + fejerStepPbDeg k D)

/-- The width-exponent degree of the next class. -/
def fejerStepExpDeg (k D : Nat) : Nat :=
  fejerStepZDeg k D + 1 + fejerStepLDeg k D + fejerStepPbDeg k D + 5

/-- The threshold degree of the next class. -/
def fejerStepThrDeg (k D : Nat) : Nat := D * (fejerStepP k + 2) + fejerStepP k + 2

/-! ### Bases -/

theorem twoDiv_budget_le_fejer {gamma theta g : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg0 : 0 < g)
    (hgi : 2 / g ≤ (2 / (gamma * theta)) ^ (32 * fejerProductExponent k + 1)) :
    2 / (g * classBudgetW (fejerThetaOne theta gamma k) k) ≤ (2 / (gamma * theta)) ^ (fejerStepP k + 1) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, -⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  have hbi := classBudgetW_fejer_inv_le k hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  rw [show 2 / (g * classBudgetW (fejerThetaOne theta gamma k) k) = 2 / g * (classBudgetW (fejerThetaOne theta gamma k) k)⁻¹ by
    field_simp]
  calc 2 / g * (classBudgetW (fejerThetaOne theta gamma k) k)⁻¹
      ≤ u ^ (32 * fejerProductExponent k + 1) * u ^ (32 * fejerProductExponent k) :=
        mul_le_mul hgi hbi (inv_pos.mpr hb).le (pow_nonneg hupos.le _)
    _ = u ^ (32 * fejerProductExponent k + 1 + 32 * fejerProductExponent k) := by rw [← pow_add]
    _ = u ^ (fejerStepP k + 1) := by
        congr 1
        unfold fejerStepP
        ring

theorem twoDiv_delta_le_fejer {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    2 / (section16Delta (fejerThetaOne theta gamma k) * classBudgetW (fejerThetaOne theta gamma k) k) ≤
      (2 / (gamma * theta)) ^ (fejerStepP k + 1) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨-, -, hd, -⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  have hdi := classDeltaW_fejer_inv_le k hg hg1 ht ht1
  refine twoDiv_budget_le_fejer k hg hg1 ht ht1 hd ?_
  rw [div_eq_mul_inv, pow_succ, mul_comm]
  exact mul_le_mul hdi hu2 (by norm_num) (pow_nonneg (by linarith) _)

theorem twoDiv_gamma_le_fejer {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    2 / (gamma * classBudgetW (fejerThetaOne theta gamma k) k) ≤ (2 / (gamma * theta)) ^ (fejerStepP k + 1) := by
  obtain ⟨hu2, -, h2g, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  refine twoDiv_budget_le_fejer k hg hg1 ht ht1 hg ?_
  have hu1 : 1 ≤ 2 / (gamma * theta) := le_trans (by norm_num) hu2
  refine h2g.trans ?_
  calc 2 / (gamma * theta) = (2 / (gamma * theta)) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ hu1 (Nat.le_add_left 1 _)

/-! ### The count -/

/-- **The count of the next class.** -/
theorem step_count_le_fejer {k D : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (famPieceGraphBound (classQr V D k (n * classPiecesFejer gamma theta k) (classBudgetW (fejerThetaOne theta gamma k) k) gamma)
        (classPb V D (n * classPiecesFejer gamma theta k) (classBudgetW (fejerThetaOne theta gamma k) k) gamma)
        (n * classPiecesFejer gamma theta k) rho)
      (((3 ^ (k + 1) * (n * classPiecesFejer gamma theta k)) : Nat) : Real) ≤
      uniformBase V' n theta gamma rho ^ fejerStepCountDeg k D := by
  obtain ⟨hw2, huw, hrw, hnw, hVw, hV'w⟩ := step_w_facts hV hVV n hg hg1 ht ht1 hr hr1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, -⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  have hm := classPiecesFejer_le_gen k hg hg1 ht ht1
  have hgd := twoDiv_gamma_le_fejer k hg hg1 ht ht1
  have hPk := fejerStepP_ge k
  have hnv := classVertexNum_succ_le k
  set w := uniformBase V' n theta gamma rho with hwdef
  set u := 2 / (gamma * theta) with hu
  set m := classPiecesFejer gamma theta k
  set tS := classBudgetW (fejerThetaOne theta gamma k) k
  clear_value w u
  have hw1 : 1 ≤ w := by linarith
  have hV0 : 0 ≤ V := by linarith
  have liftu : ∀ (x : Real) (j : Nat), x ≤ u ^ j → x ≤ w ^ j := fun x j h =>
    h.trans (pow_le_pow_left₀ (by linarith) huw j)
  have hmw := liftu _ _ hm
  have hgdw := liftu _ _ hgd
  -- the number of pieces
  have hnw1 : (n : Real) ≤ w ^ 1 := by rw [pow_one]; exact hnw
  have hM : ((n * m : Nat) : Real) ≤ w ^ (fejerStepP k + 2) :=
    le_pow_mono hw2 (by omega) (nat_mul_le_pow hw2 hnw1 hmw)
  have hM1 : ((n * m : Nat) : Real) + 1 ≤ w ^ (fejerStepP k + 2 + 1) :=
    add_le_pow_succ hw2 hM (one_le_pow_of_two_le hw2 _)
  have h3k : (((3 ^ (k + 1) * (n * m)) : Nat) : Real) ≤ w ^ (2 * (k + 1) + (fejerStepP k + 2)) := by
    have h3 : ((3 ^ (k + 1) : Nat) : Real) ≤ w ^ (2 * (k + 1)) := by
      push_cast
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith only [hw2]) _
    exact nat_mul_le_pow hw2 h3 hM
  -- the remainder count at `ρ/8`
  have hY1 : ∀ _ : Fin (classVertexNum k + 1),
      max (uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) ^ D)
        (((3 ^ (k + 1) * (n * m)) : Nat) : Real) ≤ w ^ (D * fejerStepY1 k) := by
    intro _
    have hnv0 : (0 : Real) < (classVertexNum k : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (classVertexNum k); linarith only [this]
    have hscale : 0 < rho / 8 / ((classVertexNum k : Real) + 1) :=
      div_pos (div_pos hr (by norm_num)) hnv0
    have hc : (8 : Real) * ((classVertexNum k : Real) + 1) ≤ 2 ^ (k + 3) := by
      have h1 : ((classVertexNum k : Real) + 1) ≤ 2 ^ k := by exact_mod_cast hnv
      have h2 : (2 : Real) ^ (k + 3) = 2 ^ k * 8 := by rw [pow_add]; norm_num
      rw [h2]
      linarith only [h1]
    have hc0 : (0 : Real) < 8 * ((classVertexNum k : Real) + 1) := mul_pos (by norm_num) hnv0
    have hri : (rho / 8 / ((classVertexNum k : Real) + 1))⁻¹ ≤ w ^ (k + 3 + 1) := by
      rw [div_div]
      exact inv_scale_le (c := 8 * ((classVertexNum k : Real) + 1)) (j := k + 3) hw2 hr hrw hc0 hc
    have hbase := level_base_le hw2 hV0 hVw hM1 hscale hri hg hb hgdw
    have hbase' : uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) ≤
        w ^ fejerStepY1 k := le_pow_mono hw2 (by unfold fejerStepY1; omega) hbase
    refine max_le ?_ ?_
    · rw [show D * fejerStepY1 k = fejerStepY1 k * D from Nat.mul_comm D (fejerStepY1 k), pow_mul]
      exact pow_le_pow_left₀ (uniformBase_nonneg hV _ hb hg hscale.le) hbase' D
    · refine le_pow_mono hw2 ?_ h3k
      have : fejerStepY1 k ≤ D * fejerStepY1 k := Nat.le_mul_of_pos_left _ hD
      unfold fejerStepY1 at this ⊢
      omega
  have hQr : classQr V D k (n * m) tS gamma (rho / 8) ≤ w ^ fejerStepQrDeg k D := by
    unfold classQr
    refine (Finset.prod_le_prod (fun i _ => le_max_of_le_right (Nat.cast_nonneg _))
      (fun i _ => hY1 i)).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (pow_le_pow_right₀ (one_le_pow_of_two_le hw2 _) hnv).trans (le_of_eq ?_)
    unfold fejerStepQrDeg
    rw [← pow_mul, mul_comm]
  -- the samples and the slice count
  have hS := famPieceSamples_le_power hw2 hr hrw hQr hM
  set S := famPieceSamples (classQr V D k (n * m) tS gamma) (n * m) rho
  have hMS : ((n * m * S : Nat) : Real) + 1 ≤ w ^ ((fejerStepP k + 2) + fejerStepSDeg k D + 1) :=
    add_le_pow_succ hw2 (nat_mul_le_pow hw2 hM hS) (one_le_pow_of_two_le hw2 _)
  have hr4 : (rho / 4)⁻¹ ≤ w ^ (2 + 1) := inv_scale_le hw2 hr hrw (by norm_num) (by norm_num)
  have hPbase := level_base_le hw2 hV0 hVw hMS (by positivity) hr4 hg hb hgdw
  have hPb : classPb V D (n * m) tS gamma S (rho / 4) ≤ w ^ fejerStepPbDeg k D := by
    unfold classPb
    rw [abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    have h := pow_le_pow_left₀ (uniformBase_nonneg hV _ hb hg (by positivity)) hPbase D
    rw [← pow_mul] at h
    refine h.trans (pow_le_pow_right₀ hw1 ?_)
    unfold fejerStepPbDeg
    rw [mul_comm]
    exact Nat.mul_le_mul_left D (by omega)
  have hPb0 : 0 ≤ classPb V D (n * m) tS gamma S (rho / 4) := by
    unfold classPb
    exact pow_nonneg (uniformBase_nonneg hV _ hb hg (abs_nonneg _)) _
  have hG := famPieceGraphBound_le_power hw2 hM hS hPb0 hPb
  refine max_le hG ?_
  refine le_pow_mono hw2 ?_ h3k
  have h1 : fejerStepSDeg k D + 2 * fejerStepP k + 8 ≤ fejerStepPbDeg k D := by
    unfold fejerStepPbDeg; exact Nat.le_mul_of_pos_left _ hD
  unfold fejerStepCountDeg
  unfold fejerStepSDeg at h1 ⊢
  omega

/-! ### The width exponent -/

/-- **The width exponent of the next class.** -/
theorem step_exp_inv_le_fejer {k D : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPiecesFejer gamma theta k
    let tS := classBudgetW (fejerThetaOne theta gamma k) k
    let gS := section16Delta (fejerThetaOne theta gamma k)
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho *
          famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (classQb V D M tS gS) (tightZeta (fejerThetaOne theta gamma k / 4)) rho)
          (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho)
          (famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ uniformBase V' n theta gamma rho ^ fejerStepExpDeg k D := by
  intro M tS gS e
  obtain ⟨hw2, huw, hrw, hnw, hVw, hV'w⟩ := step_w_facts hV hVV n hg hg1 ht ht1 hr hr1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, hb1⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  obtain ⟨-, -, hd, hd1⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  obtain ⟨hz0, hz1, hzi⟩ := tightZeta_fejer_inv_le_gen k hg hg1 ht ht1
  have hm := classPiecesFejer_le_gen k hg hg1 ht ht1
  have hgd := twoDiv_gamma_le_fejer k hg hg1 ht ht1
  have hdd := twoDiv_delta_le_fejer k hg hg1 ht ht1
  have hPk := fejerStepP_ge k
  have hnv := classVertexNum_succ_le k
  have hnv0 : (0 : Real) < (classVertexNum k : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (classVertexNum k); linarith only [this]
  set w := uniformBase V' n theta gamma rho with hwdef
  set u := 2 / (gamma * theta) with hu
  set m := classPiecesFejer gamma theta k
  clear_value w u
  have hw0 : 0 ≤ w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hV0 : 0 ≤ V := by linarith
  have liftu : ∀ (x : Real) (j : Nat), x ≤ u ^ j → x ≤ w ^ j := fun x j h =>
    h.trans (pow_le_pow_left₀ (by linarith) huw j)
  have hmw := liftu _ _ hm
  have hgdw := liftu _ _ hgd
  have hddw := liftu _ _ hdd
  have hnw1 : (n : Real) ≤ w ^ 1 := by rw [pow_one]; exact hnw
  have hM : ((n * m : Nat) : Real) ≤ w ^ (fejerStepP k + 2) :=
    le_pow_mono hw2 (by omega) (nat_mul_le_pow hw2 hnw1 hmw)
  have hM1 : ((n * m : Nat) : Real) + 1 ≤ w ^ (fejerStepP k + 2 + 1) :=
    add_le_pow_succ hw2 hM (one_le_pow_of_two_le hw2 _)
  -- the spectrum controls at `ρ/8`
  have hr8 : (rho / 8)⁻¹ ≤ w ^ (3 + 1) := inv_scale_le hw2 hr hrw (by norm_num) (by norm_num)
  have hSbase := level_base_le hw2 hV0 hVw hM1 (by positivity) hr8 hd hb hddw
  have hSbase' : uniformBase V (n * m) tS gS (rho / 8) ≤ w ^ (2 * fejerStepP k + 9) :=
    le_pow_mono hw2 (by omega) hSbase
  have hSbase1 : 1 ≤ uniformBase V (n * m) tS gS (rho / 8) :=
    le_trans (by norm_num) (uniformBase_two_le hV _ hb hb1 hd hd1 (by positivity)
      (by linarith only [hr1]))
  have hQb : classQb V D (n * m) tS gS (rho / 8) ≤ w ^ fejerStepEbDeg k D := by
    unfold classQb fejerStepEbDeg
    rw [show D * (2 * fejerStepP k + 9) = (2 * fejerStepP k + 9) * D from Nat.mul_comm _ _, pow_mul]
    exact pow_le_pow_left₀ (by linarith) hSbase' D
  have hEbi : (classEb V D (n * m) tS gS (rho / 8))⁻¹ ≤ w ^ fejerStepEbDeg k D := by
    unfold classEb; rw [inv_inv]; exact hQb
  have hEb0 : 0 < classEb V D (n * m) tS gS (rho / 8) := by
    unfold classEb; exact inv_pos.mpr (pow_pos (by linarith) _)
  -- the remainder exponent at `ρ/8`
  have hscale : 0 < rho / 8 / ((classVertexNum k : Real) + 1) :=
    div_pos (div_pos hr (by norm_num)) hnv0
  have hc : (8 : Real) * ((classVertexNum k : Real) + 1) ≤ 2 ^ (k + 3) := by
    have h1 : ((classVertexNum k : Real) + 1) ≤ 2 ^ k := by exact_mod_cast hnv
    have h2 : (2 : Real) ^ (k + 3) = 2 ^ k * 8 := by rw [pow_add]; norm_num
    rw [h2]; linarith only [h1]
  have hri : (rho / 8 / ((classVertexNum k : Real) + 1))⁻¹ ≤ w ^ (k + 3 + 1) := by
    rw [div_div]
    exact inv_scale_le (c := 8 * ((classVertexNum k : Real) + 1)) (j := k + 3) hw2 hr hrw
      (mul_pos (by norm_num) hnv0) hc
  have hRbase := level_base_le hw2 hV0 hVw hM1 hscale hri hg hb hgdw
  have hRbase' : uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) ≤
      w ^ fejerStepY1 k := le_pow_mono hw2 (by unfold fejerStepY1; omega) hRbase
  have hRbase1 : 1 ≤ uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) :=
    le_trans (by norm_num) (uniformBase_two_le hV _ hb hb1 hg hg1 hscale
      (by rw [div_le_one hnv0]; have := Nat.cast_nonneg (α := Real) (classVertexNum k)
          linarith only [this, hr1]))
  have hfac : (16 * uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) ^ D) ≤
      w ^ (4 + D * fejerStepY1 k) := by
    rw [pow_add]
    refine mul_le_mul (const_le_pow hw2 (by norm_num)) ?_ (pow_nonneg (by linarith) _)
      (pow_nonneg hw0 _)
    rw [show D * fejerStepY1 k = fejerStepY1 k * D from Nat.mul_comm _ _, pow_mul]
    exact pow_le_pow_left₀ (by linarith) hRbase' D
  have hEr0 : 0 < classEr V D k (n * m) tS gamma (rho / 8) := by
    unfold classEr
    refine Finset.prod_pos fun i _ => ?_
    exact div_pos (inv_pos.mpr (pow_pos (by linarith) _)) (by norm_num)
  have hEri : (classEr V D k (n * m) tS gamma (rho / 8))⁻¹ ≤ w ^ fejerStepErDeg k D := by
    unfold classEr
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow]
    set b := uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1))
    have hc' : ((b ^ D)⁻¹ / 16)⁻¹ ≤ w ^ (4 + D * fejerStepY1 k) := by
      rw [inv_div, div_inv_eq_mul]
      exact hfac
    have hc0 : 0 ≤ ((b ^ D)⁻¹ / 16)⁻¹ := by
      rw [inv_div, div_inv_eq_mul]
      exact mul_nonneg (by norm_num) (pow_nonneg (le_trans zero_le_one hRbase1) _)
    refine (pow_le_pow_left₀ hc0 hc' _).trans ?_
    refine (pow_le_pow_right₀ (one_le_pow_of_two_le hw2 _) hnv).trans (le_of_eq ?_)
    unfold fejerStepErDeg
    rw [← pow_mul]
  -- the divisor
  set q := ⌊classQb V D (n * m) tS gS (rho / 8)⌋₊ with hqdef
  have hq : (q : Real) ≤ w ^ fejerStepEbDeg k D :=
    (Nat.floor_le (by unfold classQb; exact pow_nonneg (le_trans zero_le_one hSbase1) _)).trans hQb
  have hq1 : ((q + 1 : Nat) : Real) ≤ w ^ (fejerStepEbDeg k D + 1) := by
    push_cast; exact add_le_pow_succ hw2 hq (one_le_pow_of_two_le hw2 _)
  have hBq : familyWidthDivisor k p q ≤ w ^ fejerStepBqDeg k D := by
    unfold familyWidthDivisor fejerStepBqDeg
    have hpow : (((q + 1) ^ (2 * 2 ^ (k + 1)) : Nat) : Real) ≤ w ^ ((fejerStepEbDeg k D + 1) * 2 ^ (k + 2)) := by
      rw [Nat.cast_pow]
      calc ((q + 1 : Nat) : Real) ^ (2 * 2 ^ (k + 1))
          ≤ (w ^ (fejerStepEbDeg k D + 1)) ^ (2 * 2 ^ (k + 1)) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hq1 _
        _ = w ^ ((fejerStepEbDeg k D + 1) * 2 ^ (k + 2)) := by
            rw [← pow_mul]
            congr 1
            rw [pow_succ 2 (k + 1)]
            ring
    have hpw : ((p : Nat) : Real) ≤ w ^ 1 := by rw [pow_one]; exact hpV.trans hV'w
    have h1 := nat_mul_le_pow hw2 hpw hpow
    have h2 := nat_mul_le_pow hw2 (show ((2 : Nat) : Real) ≤ w ^ 1 by rw [pow_one]; push_cast; linarith) h1
    have h3 := const_mul_le_pow (c := (4 : Real)) (j := 2) hw2 (by norm_num) (by norm_num) (Nat.cast_nonneg _) h2
    refine h3.trans (pow_le_pow_right₀ hw1 ?_)
    omega
  have hBq0 : 0 < familyWidthDivisor k p q := familyWidthDivisor_pos hp q
  -- the line exponent
  set L := pieceLineExponent (familyWidthDivisor k p) (classQb V D (n * m) tS gS)
    (classEb V D (n * m) tS gS) (classEr V D k (n * m) tS gamma) rho with hLdef
  have hL0 : 0 < L := by
    rw [hLdef]; unfold pieceLineExponent
    exact div_pos (mul_pos hEr0 hEb0) hBq0
  have hLi : L⁻¹ ≤ w ^ fejerStepLDeg k D := by
    rw [hLdef]; unfold pieceLineExponent
    rw [inv_div, div_eq_mul_inv, mul_inv]
    rw [← hqdef]
    exact mul_le_pow_add (mul_nonneg (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le)
      hBq (mul_le_pow_add (inv_pos.mpr hEb0).le hEri hEbi hw0) hw0
  -- the slice exponent
  have hQr : classQr V D k (n * m) tS gamma (rho / 8) ≤ w ^ fejerStepQrDeg k D := by
    unfold classQr
    refine (Finset.prod_le_prod (g := fun _ => w ^ (D * fejerStepY1 k))
      (fun i _ => le_max_of_le_right (Nat.cast_nonneg _)) ?_).trans ?_
    · intro i _
      refine max_le ?_ ?_
      · rw [show D * fejerStepY1 k = fejerStepY1 k * D from Nat.mul_comm _ _, pow_mul]
        exact pow_le_pow_left₀ (by linarith) hRbase' D
      · have h3 : ((3 ^ (k + 1) : Nat) : Real) ≤ w ^ (2 * (k + 1)) := by
          push_cast; rw [pow_mul]
          exact pow_le_pow_left₀ (by norm_num) (by nlinarith only [hw2]) _
        refine le_pow_mono hw2 ?_ (nat_mul_le_pow hw2 h3 hM)
        have : fejerStepY1 k ≤ D * fejerStepY1 k := Nat.le_mul_of_pos_left _ hD
        unfold fejerStepY1 at this ⊢
        omega
    · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      refine (pow_le_pow_right₀ (one_le_pow_of_two_le hw2 _) hnv).trans (le_of_eq ?_)
      unfold fejerStepQrDeg
      rw [← pow_mul, mul_comm]
  have hS := famPieceSamples_le_power hw2 hr hrw hQr hM
  set S := famPieceSamples (classQr V D k (n * m) tS gamma) (n * m) rho with hSdef
  have hMS : ((n * m * S : Nat) : Real) + 1 ≤ w ^ ((fejerStepP k + 2) + fejerStepSDeg k D + 1) :=
    add_le_pow_succ hw2 (nat_mul_le_pow hw2 hM hS) (one_le_pow_of_two_le hw2 _)
  have hr4 : (rho / 4)⁻¹ ≤ w ^ (2 + 1) := inv_scale_le hw2 hr hrw (by norm_num) (by norm_num)
  have hPbase := level_base_le hw2 hV0 hVw hMS (by positivity) hr4 hg hb hgdw
  have hPbase1 : 1 ≤ uniformBase V (n * m * S) tS gamma (rho / 4) :=
    le_trans (by norm_num) (uniformBase_two_le hV _ hb hb1 hg hg1 (by positivity)
      (by linarith only [hr1]))
  set Sl := famPieceSliceExponent (classQr V D k (n * m) tS gamma) (classEs V D (n * m) tS gamma)
    (n * m) rho with hSldef
  have hSlval : Sl = (uniformBase V (n * m * S) tS gamma (rho / 4) ^ D)⁻¹ := by
    rw [hSldef]
    unfold famPieceSliceExponent classEs
    rw [← hSdef, abs_of_pos (by positivity : (0 : Real) < rho / 4)]
  have hSl0 : 0 < Sl := by rw [hSlval]; exact inv_pos.mpr (pow_pos (by linarith) _)
  have hSl1 : Sl ≤ 1 := by rw [hSlval]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hPbase1)
  have hSli : Sl⁻¹ ≤ w ^ fejerStepPbDeg k D := by
    rw [hSlval, inv_inv]
    have h := pow_le_pow_left₀ (by linarith) hPbase D
    rw [← pow_mul] at h
    refine h.trans (pow_le_pow_right₀ hw1 ?_)
    unfold fejerStepPbDeg
    rw [mul_comm]
    exact Nat.mul_le_mul_left D (by omega)
  -- the width scale
  have hA1 : 1 ≤ familyWidthPrefactor K q := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((K * (q + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  have hA : familyWidthPrefactor K q ≤ w ^ (fejerStepEbDeg k D + 4) := by
    unfold familyWidthPrefactor
    have hKw : ((K : Nat) : Real) ≤ w ^ 1 := by rw [pow_one]; exact hKV.trans hV'w
    have h1 := nat_mul_le_pow hw2 hKw hq1
    have h2 := const_mul_le_pow (c := (4 : Real)) (j := 2) hw2 (by norm_num) (by norm_num) (Nat.cast_nonneg _) h1
    exact h2.trans (pow_le_pow_right₀ hw1 (by omega))
  set z := pieceWidthScale (familyWidthPrefactor K) (classQb V D (n * m) tS gS)
    (tightZeta (fejerThetaOne theta gamma k / 4)) rho with hzdef
  have hzval : z = tightZeta (fejerThetaOne theta gamma k / 4) / familyWidthPrefactor K q := by rw [hzdef]; rfl
  have hzpos : 0 < z := by rw [hzval]; exact div_pos hz0 (lt_of_lt_of_le zero_lt_one hA1)
  have hzle : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact hz1.trans hA1
  have hzinv : z⁻¹ ≤ Real.exp (w ^ (fejerStepZDeg k D + 1)) := by
    rw [hzval, inv_div, div_eq_mul_inv]
    have hAe : familyWidthPrefactor K q ≤ Real.exp (w ^ fejerStepZDeg k D) :=
      le_exp_pow_of_le_pow (le_pow_mono hw2 (by unfold fejerStepZDeg; omega) hA)
    have hze : (tightZeta (fejerThetaOne theta gamma k / 4))⁻¹ ≤ Real.exp (w ^ fejerStepZDeg k D) := by
      refine hzi.trans (Real.exp_le_exp.mpr ?_)
      refine (pow_le_pow_left₀ (by linarith) huw _).trans (pow_le_pow_right₀ hw1 ?_)
      unfold fejerStepZDeg fejerStepT
      omega
    exact exp_mul_le hw2 (inv_pos.mpr hz0).le hAe hze
  -- the cap
  have hnz : 6 ≤ fejerStepZDeg k D + 1 := by
    unfold fejerStepZDeg fejerStepT
    omega
  have hfin := capped_rounded_inv_le hw2 hnz hL0 hLi hSl0 hSl1 hSli hzpos hzle hzinv
  exact ⟨section16CappedWidthExponent_pos (div_pos (mul_pos hL0 hSl0) (by norm_num)), hfin⟩


/-! ### The threshold -/

theorem step_thr_le_fejer {k D : Nat} (hk : 1 ≤ k) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    classStepThresholdFejer V D theta gamma k ≤ (V' * (2 / (gamma * theta))) ^ fejerStepThrDeg k D := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hL := fejerProductThreshold_le_gen hk hg hg1 ht ht1
  have hgd := twoDiv_gamma_le_fejer k hg hg1 ht ht1
  have hdd := twoDiv_delta_le_fejer k hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hV' : 1 ≤ V' := hV.trans hVV
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hua : u ≤ V' * u := le_mul_of_one_le_left (by linarith) hV'
  have ha2 : 2 ≤ V' * u := hu2.trans hua
  have ha1 : 1 ≤ V' * u := le_trans (by norm_num) ha2
  have hpow : ∀ j : Nat, V * u ^ j ≤ (V' * u) ^ (j + 1) := by
    intro j
    rw [pow_succ']
    exact mul_le_mul (hVV.trans (le_mul_of_one_le_right (by linarith) hu1))
      (pow_le_pow_left₀ (by linarith) hua j) (pow_nonneg (by linarith) _) (by linarith)
  have hpiece : ∀ g : Real, 0 < g → 2 / (g * classBudgetW (fejerThetaOne theta gamma k) k) ≤ u ^ (fejerStepP k + 1) →
      (V * (2 / (g * classBudgetW (fejerThetaOne theta gamma k) k))) ^ D ≤ (V' * u) ^ fejerStepThrDeg k D := by
    intro g hg0 hgi
    have h1 : V * (2 / (g * classBudgetW (fejerThetaOne theta gamma k) k)) ≤ (V' * u) ^ (fejerStepP k + 1 + 1) :=
      (mul_le_mul_of_nonneg_left hgi (by linarith)).trans (hpow _)
    have h0 : 0 ≤ V * (2 / (g * classBudgetW (fejerThetaOne theta gamma k) k)) := by
      obtain ⟨hb, -⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
      have : 0 < g * classBudgetW (fejerThetaOne theta gamma k) k := mul_pos hg0 hb
      exact mul_nonneg (by linarith) (div_nonneg (by norm_num) this.le)
    have h2 := pow_le_pow_left₀ h0 h1 D
    rw [← pow_mul] at h2
    refine h2.trans (pow_le_pow_right₀ ha1 ?_)
    unfold fejerStepThrDeg
    have : (fejerStepP k + 1 + 1) * D = D * (fejerStepP k + 2) := by ring
    omega
  unfold classStepThresholdFejer classPieceThresholdW
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · have h3 : (3 : Real) ≤ (V' * u) ^ 2 := by nlinarith only [ha2]
    exact h3.trans (pow_le_pow_right₀ ha1 (by unfold fejerStepThrDeg; omega))
  · refine hL.trans ((pow_le_pow_left₀ (by linarith) hua _).trans (pow_le_pow_right₀ ha1 ?_))
    unfold fejerStepThrDeg
    omega
  · obtain ⟨-, -, hd, -⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
    exact hpiece _ hd hdd
  · exact hpiece _ hg hgd

/-! ### The step -/

/-- **The step of route (II).** A uniform class of dimension `k ≥ 1` at one
degree `D`, with the family Lemma 16.6 at dimension `k`, gives a uniform class
of dimension `k+1`. -/
theorem powerUniformClass_succ_fejer {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V) {D : Nat}
    (hD : 1 ≤ D) (C : PowerUniformClass k V D D D) {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    Nonempty (PowerUniformClass (k + 1) V' (fejerStepCountDeg k D) (fejerStepExpDeg k D) (fejerStepThrDeg k D)) := by
  classical
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (classPiecesFejer gamma theta k) → StepPieceFejer C N theta gamma,
        Gamma ⊆ stepPieceFejerGraphs C P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => ClassPiece.empty C _ _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    have hN' : classStepThresholdFejer V D theta gamma k ≤ N :=
      (step_thr_le_fejer hk hV hVV hg hg1 ht ht1).trans hN
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp_fejer C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover_fejer C hk hV (familyWidthPrefactor_pos hK) (familyWidthDivisor_pos hp)
      hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      exact step_count_le_fejer hD hV hVV hg hg1 ht ht1 hr hr1 n
    · intro rho hr hr1
      have h2 := uniformBase_two_le (hV.trans hVV) n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := step_exp_inv_le_fejer hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      have := inv_anti₀ (inv_pos.mpr he0) hei
      rwa [inv_inv] at this
end LeanProofs.GowersSzemeredi
