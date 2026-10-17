import GowersSzemeredi.Proofs18ExponentialProduct
import GowersSzemeredi.Proofs16ClassStep

/-! The step of route (II) with power controls (Notes L.6, E5 part B).

Given a uniform class of dimension `k ≥ 1` at one degree `D`, and the family
Lemma 16.6 at dimension `k` with constants `K, p ≤ V′`, the relations covered
by step pieces form a uniform class of dimension `k+1` at base `V′`, with
explicit degrees:
* `stepCountDeg k D` for the count;
* `stepExpDeg k D` for the width exponent;
* `stepThrDeg k D` for the threshold.

The bounds are computed in the base `w = uniformBase V′ n θ γ ρ` of the new
class, with `P = stepP k = 2^(2^(k+5)+6)` (Part A) and
`T = 2^(2^(k+6))` (the Bohr radius). All intermediate degrees are named, so
every absorption is a linear inequality for `omega`.

* `step_count_le`, `step_exp_inv_le`, `step_thr_le`: the three bounds.
* `PowerUniformClass.weaken`: a class is a class at any larger base and
  degrees.
* `powerUniformClass_succ`: **the step of route (II)**. A uniform class of
  dimension `k ≥ 1` at degree `D`, with the family Lemma 16.6 at dimension
  `k`, gives a uniform class of dimension `k+1` at base `V′` and degrees
  `(stepCountDeg k D, stepExpDeg k D, stepThrDeg k D)`.

Trap: `positivity` unfolds definitions such as `classVertexNum k` (a
`Finset.card` over `Fin k → Bool`) and diverges in `whnf` for symbolic `k`.
Nonnegativity of such terms is therefore supplied by hand.

`classPieces_le_stepP`, `powerUniformClass_succ`, `stepP_ge`, `step_count_le`,
`step_exp_inv_le`, `step_thr_le`, `twoDiv_budget_le`, `twoDiv_delta_le` and
`twoDiv_gamma_le` are in `Proofs16ClassStepDegreesSide`, outside the final
route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The degrees -/

/-- The parameter exponent of Part A: `2^(2^(k+5)+6)`. -/
def stepP (k : Nat) : Nat := 2 ^ (2 ^ (k + 5) + 6)

/-- The Bohr exponent: `2^(2^(k+6))`. -/
def stepT (k : Nat) : Nat := 2 ^ (2 ^ (k + 6))

def stepY1 (k : Nat) : Nat := 2 * stepP k + k + 9
def stepQrDeg (k D : Nat) : Nat := 2 ^ k * (D * stepY1 k)
def stepSDeg (k D : Nat) : Nat := stepQrDeg k D + (stepP k + 2) + 7
def stepPbDeg (k D : Nat) : Nat := D * (stepSDeg k D + 2 * stepP k + 8)
def stepEbDeg (k D : Nat) : Nat := D * (2 * stepP k + 9)
def stepErDeg (k D : Nat) : Nat := (4 + D * stepY1 k) * 2 ^ k
def stepBqDeg (k D : Nat) : Nat := 4 + (stepEbDeg k D + 1) * 2 ^ (k + 2)
def stepLDeg (k D : Nat) : Nat := stepBqDeg k D + (stepErDeg k D + stepEbDeg k D)
def stepZDeg (k D : Nat) : Nat := stepT k + stepEbDeg k D + 4

/-- The count degree of the next class. -/
def stepCountDeg (k D : Nat) : Nat :=
  (stepP k + 2) + (2 * stepSDeg k D + stepPbDeg k D + stepPbDeg k D)

/-- The width-exponent degree of the next class. -/
def stepExpDeg (k D : Nat) : Nat :=
  stepZDeg k D + 1 + stepLDeg k D + stepPbDeg k D + 5

/-- The threshold degree of the next class. -/
def stepThrDeg (k D : Nat) : Nat := D * (stepP k + 2) + stepP k + 2

/-! ### The degrees at any parameter exponent `P` and Bohr exponent `T`

The degrees above are these at `P = stepP k`, `T = stepT k`, and the Fejér
degrees of `Proofs16ClassStepDegreesFejer` are these at `fejerStepP k`,
`fejerStepT k` (both by `rfl`). -/

def stepY1W (P k : Nat) : Nat := 2 * P + k + 9
def stepQrDegW (P k D : Nat) : Nat := 2 ^ k * (D * stepY1W P k)
def stepSDegW (P k D : Nat) : Nat := stepQrDegW P k D + (P + 2) + 7
def stepPbDegW (P k D : Nat) : Nat := D * (stepSDegW P k D + 2 * P + 8)
def stepEbDegW (P D : Nat) : Nat := D * (2 * P + 9)
def stepErDegW (P k D : Nat) : Nat := (4 + D * stepY1W P k) * 2 ^ k
def stepBqDegW (P k D : Nat) : Nat := 4 + (stepEbDegW P D + 1) * 2 ^ (k + 2)
def stepLDegW (P k D : Nat) : Nat := stepBqDegW P k D + (stepErDegW P k D + stepEbDegW P D)
def stepZDegW (P T D : Nat) : Nat := T + stepEbDegW P D + 4
def stepCountDegW (P k D : Nat) : Nat :=
  (P + 2) + (2 * stepSDegW P k D + stepPbDegW P k D + stepPbDegW P k D)
def stepExpDegW (P T k D : Nat) : Nat :=
  stepZDegW P T D + 1 + stepLDegW P k D + stepPbDegW P k D + 5

/-! ### Bases -/

/-- A level-`k` base, in the base `w` of the next class. -/
theorem level_base_le {V w g thp rho' : Real} {M' : Nat} {a b c : Nat} (hw : 2 ≤ w)
    (hV0 : 0 ≤ V) (hVw : V ≤ w) (hM : (M' : Real) + 1 ≤ w ^ a) (hrho : 0 < rho')
    (hri : rho'⁻¹ ≤ w ^ b) (hg0 : 0 < g) (hthp : 0 < thp) (hgd : 2 / (g * thp) ≤ w ^ c) :
    uniformBase V M' thp g rho' ≤ w ^ (a + 1 + c + b) := by
  have hw0 : 0 ≤ w := by linarith
  unfold uniformBase
  rw [show 2 / (g * thp * rho') = 2 / (g * thp) * rho'⁻¹ by field_simp]
  have h1 : ((M' : Real) + 1) * V ≤ w ^ a * w ^ 1 := by
    rw [pow_one]; exact mul_le_mul hM hVw hV0 (pow_nonneg hw0 _)
  have h2 : 2 / (g * thp) * rho'⁻¹ ≤ w ^ c * w ^ b :=
    mul_le_mul hgd hri (inv_pos.mpr hrho).le (pow_nonneg hw0 _)
  have h0 : 0 ≤ 2 / (g * thp) * rho'⁻¹ := by positivity
  calc ((M' : Real) + 1) * V * (2 / (g * thp) * rho'⁻¹)
      ≤ w ^ a * w ^ 1 * (w ^ c * w ^ b) :=
        mul_le_mul h1 h2 h0 (by positivity)
    _ = w ^ (a + 1 + c + b) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf

/-! ### Shared facts -/

theorem classVertexNum_succ_le (k : Nat) : classVertexNum k + 1 ≤ 2 ^ k := by
  unfold classVertexNum
  have h : (otherVertices k).card ≤ 2 ^ k := by
    unfold otherVertices
    refine (Finset.card_filter_le _ _).trans ?_
    simp [Finset.card_univ]
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- The facts about the base `w` of the next class used throughout. -/
theorem step_w_facts {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V') (n : Nat) {theta gamma rho : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho)
    (hr1 : rho ≤ 1) :
    2 ≤ uniformBase V' n theta gamma rho ∧ 2 / (gamma * theta) ≤ uniformBase V' n theta gamma rho ∧
      rho⁻¹ ≤ uniformBase V' n theta gamma rho ∧ (n : Real) ≤ uniformBase V' n theta gamma rho ∧
      V ≤ uniformBase V' n theta gamma rho ∧ V' ≤ uniformBase V' n theta gamma rho := by
  have hV' : 1 ≤ V' := hV.trans hVV
  obtain ⟨hvw, hrw, hnw, hVw, hw2⟩ := uniformBase_facts hV' n hg hg1 ht ht1 hr hr1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hV'w : V' ≤ uniformBase V' n theta gamma rho := by
    exact le_trans (le_mul_of_one_le_right (by linarith) (le_trans (by norm_num) hu2)) hVw
  exact ⟨hw2, hvw, hrw, by linarith, hVV.trans hV'w, hV'w⟩

theorem inv_scale_le {w rho : Real} {c : Real} {j : Nat} (hw : 2 ≤ w) (hr : 0 < rho)
    (hrw : rho⁻¹ ≤ w) (hc0 : 0 < c) (hc : c ≤ 2 ^ j) : (rho / c)⁻¹ ≤ w ^ (j + 1) := by
  rw [inv_div, div_eq_mul_inv, pow_succ]
  exact mul_le_mul (const_le_pow hw hc) hrw (inv_pos.mpr hr).le (pow_nonneg (by linarith) _)

/-! ### The count -/

/-! ### The width exponent -/

/-- **The count of the next class**, from the class-step bounds at `P`. -/
theorem step_count_le_W {k D P : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) {m : Nat} {tS : Real} (hb : 0 < tS)
    (hm : (m : Real) ≤ (2 / (gamma * theta)) ^ P)
    (hgd : 2 / (gamma * tS) ≤ (2 / (gamma * theta)) ^ (P + 1)) (hPk : k + 8 ≤ P) :
    max (famPieceGraphBound (classQr V D k (n * m) (tS) gamma)
        (classPb V D (n * m) (tS) gamma)
        (n * m) rho)
      (((3 ^ (k + 1) * (n * m)) : Nat) : Real) ≤
      uniformBase V' n theta gamma rho ^ stepCountDegW P k D := by
  obtain ⟨hw2, huw, hrw, hnw, hVw, hV'w⟩ := step_w_facts hV hVV n hg hg1 ht ht1 hr hr1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hnv := classVertexNum_succ_le k
  set w := uniformBase V' n theta gamma rho with hwdef
  set u := 2 / (gamma * theta) with hu
  clear_value w u
  have hw1 : 1 ≤ w := by linarith
  have hV0 : 0 ≤ V := by linarith
  have liftu : ∀ (x : Real) (j : Nat), x ≤ u ^ j → x ≤ w ^ j := fun x j h =>
    h.trans (pow_le_pow_left₀ (by linarith) huw j)
  have hmw := liftu _ _ hm
  have hgdw := liftu _ _ hgd
  -- the number of pieces
  have hnw1 : (n : Real) ≤ w ^ 1 := by rw [pow_one]; exact hnw
  have hM : ((n * m : Nat) : Real) ≤ w ^ (P + 2) :=
    le_pow_mono hw2 (by omega) (nat_mul_le_pow hw2 hnw1 hmw)
  have hM1 : ((n * m : Nat) : Real) + 1 ≤ w ^ (P + 2 + 1) :=
    add_le_pow_succ hw2 hM (one_le_pow_of_two_le hw2 _)
  have h3k : (((3 ^ (k + 1) * (n * m)) : Nat) : Real) ≤ w ^ (2 * (k + 1) + (P + 2)) := by
    have h3 : ((3 ^ (k + 1) : Nat) : Real) ≤ w ^ (2 * (k + 1)) := by
      push_cast
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith only [hw2]) _
    exact nat_mul_le_pow hw2 h3 hM
  -- the remainder count at `ρ/8`
  have hY1 : ∀ _ : Fin (classVertexNum k + 1),
      max (uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) ^ D)
        (((3 ^ (k + 1) * (n * m)) : Nat) : Real) ≤ w ^ (D * stepY1W P k) := by
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
        w ^ stepY1W P k := le_pow_mono hw2 (by unfold stepY1W; omega) hbase
    refine max_le ?_ ?_
    · rw [show D * stepY1W P k = stepY1W P k * D from Nat.mul_comm D (stepY1W P k), pow_mul]
      exact pow_le_pow_left₀ (uniformBase_nonneg hV _ hb hg hscale.le) hbase' D
    · refine le_pow_mono hw2 ?_ h3k
      have : stepY1W P k ≤ D * stepY1W P k := Nat.le_mul_of_pos_left _ hD
      unfold stepY1W at this ⊢
      omega
  have hQr : classQr V D k (n * m) tS gamma (rho / 8) ≤ w ^ stepQrDegW P k D := by
    unfold classQr
    refine (Finset.prod_le_prod (fun i _ => le_max_of_le_right (Nat.cast_nonneg _))
      (fun i _ => hY1 i)).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (pow_le_pow_right₀ (one_le_pow_of_two_le hw2 _) hnv).trans (le_of_eq ?_)
    unfold stepQrDegW
    rw [← pow_mul, mul_comm]
  -- the samples and the slice count
  have hS := famPieceSamples_le_power hw2 hr hrw hQr hM
  set S := famPieceSamples (classQr V D k (n * m) tS gamma) (n * m) rho
  have hMS : ((n * m * S : Nat) : Real) + 1 ≤ w ^ ((P + 2) + stepSDegW P k D + 1) :=
    add_le_pow_succ hw2 (nat_mul_le_pow hw2 hM hS) (one_le_pow_of_two_le hw2 _)
  have hr4 : (rho / 4)⁻¹ ≤ w ^ (2 + 1) := inv_scale_le hw2 hr hrw (by norm_num) (by norm_num)
  have hPbase := level_base_le hw2 hV0 hVw hMS (by positivity) hr4 hg hb hgdw
  have hPb : classPb V D (n * m) tS gamma S (rho / 4) ≤ w ^ stepPbDegW P k D := by
    unfold classPb
    rw [abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    have h := pow_le_pow_left₀ (uniformBase_nonneg hV _ hb hg (by positivity)) hPbase D
    rw [← pow_mul] at h
    refine h.trans (pow_le_pow_right₀ hw1 ?_)
    unfold stepPbDegW
    rw [mul_comm]
    exact Nat.mul_le_mul_left D (by omega)
  have hPb0 : 0 ≤ classPb V D (n * m) tS gamma S (rho / 4) := by
    unfold classPb
    exact pow_nonneg (uniformBase_nonneg hV _ hb hg (abs_nonneg _)) _
  have hG := famPieceGraphBound_le_power hw2 hM hS hPb0 hPb
  refine max_le hG ?_
  refine le_pow_mono hw2 ?_ h3k
  have h1 : stepSDegW P k D + 2 * P + 8 ≤ stepPbDegW P k D := by
    unfold stepPbDegW; exact Nat.le_mul_of_pos_left _ hD
  unfold stepCountDegW
  unfold stepSDegW at h1 ⊢
  omega

/-! ### The threshold -/

/-- **The width exponent of the next class**, from the class-step bounds at `(P, T)`. -/
theorem step_exp_inv_le_W {k D P T : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) {m : Nat} {tS gS zeta : Real}
    (hb : 0 < tS) (hb1 : tS ≤ 1) (hd : 0 < gS) (hd1 : gS ≤ 1)
    (hz : 0 < zeta ∧ zeta ≤ 1 ∧ zeta⁻¹ ≤ Real.exp ((2 / (gamma * theta)) ^ T))
    (hm : (m : Real) ≤ (2 / (gamma * theta)) ^ P)
    (hgd : 2 / (gamma * tS) ≤ (2 / (gamma * theta)) ^ (P + 1))
    (hdd : 2 / (gS * tS) ≤ (2 / (gamma * theta)) ^ (P + 1)) (hPk : k + 8 ≤ P) :
    let M := n * m
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho *
          famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (classQb V D M tS gS) (zeta) rho)
          (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho)
          (famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ uniformBase V' n theta gamma rho ^ stepExpDegW P T k D := by
  intro M e
  obtain ⟨hw2, huw, hrw, hnw, hVw, hV'w⟩ := step_w_facts hV hVV n hg hg1 ht ht1 hr hr1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hz0, hz1, hzi⟩ := hz
  have hnv := classVertexNum_succ_le k
  have hnv0 : (0 : Real) < (classVertexNum k : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (classVertexNum k); linarith only [this]
  set w := uniformBase V' n theta gamma rho with hwdef
  set u := 2 / (gamma * theta) with hu
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
  have hM : ((n * m : Nat) : Real) ≤ w ^ (P + 2) :=
    le_pow_mono hw2 (by omega) (nat_mul_le_pow hw2 hnw1 hmw)
  have hM1 : ((n * m : Nat) : Real) + 1 ≤ w ^ (P + 2 + 1) :=
    add_le_pow_succ hw2 hM (one_le_pow_of_two_le hw2 _)
  -- the spectrum controls at `ρ/8`
  have hr8 : (rho / 8)⁻¹ ≤ w ^ (3 + 1) := inv_scale_le hw2 hr hrw (by norm_num) (by norm_num)
  have hSbase := level_base_le hw2 hV0 hVw hM1 (by positivity) hr8 hd hb hddw
  have hSbase' : uniformBase V (n * m) tS gS (rho / 8) ≤ w ^ (2 * P + 9) :=
    le_pow_mono hw2 (by omega) hSbase
  have hSbase1 : 1 ≤ uniformBase V (n * m) tS gS (rho / 8) :=
    le_trans (by norm_num) (uniformBase_two_le hV _ hb hb1 hd hd1 (by positivity)
      (by linarith only [hr1]))
  have hQb : classQb V D (n * m) tS gS (rho / 8) ≤ w ^ stepEbDegW P D := by
    unfold classQb stepEbDegW
    rw [show D * (2 * P + 9) = (2 * P + 9) * D from Nat.mul_comm _ _, pow_mul]
    exact pow_le_pow_left₀ (by linarith) hSbase' D
  have hEbi : (classEb V D (n * m) tS gS (rho / 8))⁻¹ ≤ w ^ stepEbDegW P D := by
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
      w ^ stepY1W P k := le_pow_mono hw2 (by unfold stepY1W; omega) hRbase
  have hRbase1 : 1 ≤ uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) :=
    le_trans (by norm_num) (uniformBase_two_le hV _ hb hb1 hg hg1 hscale
      (by rw [div_le_one hnv0]; have := Nat.cast_nonneg (α := Real) (classVertexNum k)
          linarith only [this, hr1]))
  have hfac : (16 * uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) ^ D) ≤
      w ^ (4 + D * stepY1W P k) := by
    rw [pow_add]
    refine mul_le_mul (const_le_pow hw2 (by norm_num)) ?_ (pow_nonneg (by linarith) _)
      (pow_nonneg hw0 _)
    rw [show D * stepY1W P k = stepY1W P k * D from Nat.mul_comm _ _, pow_mul]
    exact pow_le_pow_left₀ (by linarith) hRbase' D
  have hEr0 : 0 < classEr V D k (n * m) tS gamma (rho / 8) := by
    unfold classEr
    exact Finset.prod_pos fun i _ => (div_pos (inv_pos.mpr (pow_pos (by linarith) _)) (by norm_num))
  have hEri : (classEr V D k (n * m) tS gamma (rho / 8))⁻¹ ≤ w ^ stepErDegW P k D := by
    unfold classEr
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow]
    set b := uniformBase V (n * m) tS gamma (rho / 8 / ((classVertexNum k : Real) + 1))
    have hc' : ((b ^ D)⁻¹ / 16)⁻¹ ≤ w ^ (4 + D * stepY1W P k) := by
      rw [inv_div, div_inv_eq_mul]
      exact hfac
    have hc0 : 0 ≤ ((b ^ D)⁻¹ / 16)⁻¹ := by
      rw [inv_div, div_inv_eq_mul]
      exact mul_nonneg (by norm_num) (pow_nonneg (le_trans zero_le_one hRbase1) _)
    refine (pow_le_pow_left₀ hc0 hc' _).trans ?_
    refine (pow_le_pow_right₀ (one_le_pow_of_two_le hw2 _) hnv).trans (le_of_eq ?_)
    unfold stepErDegW
    rw [← pow_mul]
  -- the divisor
  set q := ⌊classQb V D (n * m) tS gS (rho / 8)⌋₊ with hqdef
  have hq : (q : Real) ≤ w ^ stepEbDegW P D :=
    (Nat.floor_le (by unfold classQb; exact pow_nonneg (le_trans zero_le_one hSbase1) _)).trans hQb
  have hq1 : ((q + 1 : Nat) : Real) ≤ w ^ (stepEbDegW P D + 1) := by
    push_cast; exact add_le_pow_succ hw2 hq (one_le_pow_of_two_le hw2 _)
  have hBq : familyWidthDivisor k p q ≤ w ^ stepBqDegW P k D := by
    unfold familyWidthDivisor stepBqDegW
    have hpow : (((q + 1) ^ (2 * 2 ^ (k + 1)) : Nat) : Real) ≤ w ^ ((stepEbDegW P D + 1) * 2 ^ (k + 2)) := by
      rw [Nat.cast_pow]
      calc ((q + 1 : Nat) : Real) ^ (2 * 2 ^ (k + 1))
          ≤ (w ^ (stepEbDegW P D + 1)) ^ (2 * 2 ^ (k + 1)) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hq1 _
        _ = w ^ ((stepEbDegW P D + 1) * 2 ^ (k + 2)) := by
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
  have hLi : L⁻¹ ≤ w ^ stepLDegW P k D := by
    rw [hLdef]; unfold pieceLineExponent
    rw [inv_div, div_eq_mul_inv, mul_inv, ← hqdef]
    exact mul_le_pow_add (mul_nonneg (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le)
      hBq (mul_le_pow_add (inv_pos.mpr hEb0).le hEri hEbi hw0) hw0
  -- the slice exponent
  have hQr : classQr V D k (n * m) tS gamma (rho / 8) ≤ w ^ stepQrDegW P k D := by
    unfold classQr
    refine (Finset.prod_le_prod (g := fun _ => w ^ (D * stepY1W P k))
      (fun i _ => le_max_of_le_right (Nat.cast_nonneg _)) ?_).trans ?_
    · intro i _
      refine max_le ?_ ?_
      · rw [show D * stepY1W P k = stepY1W P k * D from Nat.mul_comm _ _, pow_mul]
        exact pow_le_pow_left₀ (by linarith) hRbase' D
      · have h3 : ((3 ^ (k + 1) : Nat) : Real) ≤ w ^ (2 * (k + 1)) := by
          push_cast; rw [pow_mul]
          exact pow_le_pow_left₀ (by norm_num) (by nlinarith only [hw2]) _
        refine le_pow_mono hw2 ?_ (nat_mul_le_pow hw2 h3 hM)
        have : stepY1W P k ≤ D * stepY1W P k := Nat.le_mul_of_pos_left _ hD
        unfold stepY1W at this ⊢
        omega
    · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      refine (pow_le_pow_right₀ (one_le_pow_of_two_le hw2 _) hnv).trans (le_of_eq ?_)
      unfold stepQrDegW
      rw [← pow_mul, mul_comm]
  have hS := famPieceSamples_le_power hw2 hr hrw hQr hM
  set S := famPieceSamples (classQr V D k (n * m) tS gamma) (n * m) rho with hSdef
  have hMS : ((n * m * S : Nat) : Real) + 1 ≤ w ^ ((P + 2) + stepSDegW P k D + 1) :=
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
  have hSli : Sl⁻¹ ≤ w ^ stepPbDegW P k D := by
    rw [hSlval, inv_inv]
    have h := pow_le_pow_left₀ (by linarith) hPbase D
    rw [← pow_mul] at h
    refine h.trans (pow_le_pow_right₀ hw1 ?_)
    unfold stepPbDegW
    rw [mul_comm]
    exact Nat.mul_le_mul_left D (by omega)
  -- the width scale
  have hA1 : 1 ≤ familyWidthPrefactor K q := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((K * (q + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  have hA : familyWidthPrefactor K q ≤ w ^ (stepEbDegW P D + 4) := by
    unfold familyWidthPrefactor
    have hKw : ((K : Nat) : Real) ≤ w ^ 1 := by rw [pow_one]; exact hKV.trans hV'w
    have h1 := nat_mul_le_pow hw2 hKw hq1
    have h2 := const_mul_le_pow (c := (4 : Real)) (j := 2) hw2 (by norm_num) (by norm_num) (Nat.cast_nonneg _) h1
    exact h2.trans (pow_le_pow_right₀ hw1 (by omega))
  set z := pieceWidthScale (familyWidthPrefactor K) (classQb V D (n * m) tS gS)
    (zeta) rho with hzdef
  have hzval : z = zeta / familyWidthPrefactor K q := by rw [hzdef]; rfl
  have hzpos : 0 < z := by rw [hzval]; exact div_pos hz0 (lt_of_lt_of_le zero_lt_one hA1)
  have hzle : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact hz1.trans hA1
  have hzinv : z⁻¹ ≤ Real.exp (w ^ (stepZDegW P T D + 1)) := by
    rw [hzval, inv_div, div_eq_mul_inv]
    have hAe : familyWidthPrefactor K q ≤ Real.exp (w ^ stepZDegW P T D) :=
      le_exp_pow_of_le_pow (le_pow_mono hw2 (by unfold stepZDegW; omega) hA)
    have hze : (zeta)⁻¹ ≤ Real.exp (w ^ stepZDegW P T D) := by
      refine hzi.trans (Real.exp_le_exp.mpr ?_)
      refine (pow_le_pow_left₀ (by linarith) huw _).trans (pow_le_pow_right₀ hw1 ?_)
      unfold stepZDegW
      omega
    exact exp_mul_le hw2 (inv_pos.mpr hz0).le hAe hze
  -- the cap
  have hnz : 6 ≤ stepZDegW P T D + 1 := by
    have : 1 ≤ stepEbDegW P D := Nat.mul_pos (by omega) (by omega)
    unfold stepZDegW
    omega
  have hfin := capped_rounded_inv_le hw2 hnz hL0 hLi hSl0 hSl1 hSli hzpos hzle hzinv
  exact ⟨section16CappedWidthExponent_pos (div_pos (mul_pos hL0 hSl0) (by norm_num)), hfin⟩

/-! ### Weakening a class -/

theorem uniformBase_mono_V {V V' : Real} (hVV : V ≤ V') (n : Nat) {theta gamma rho : Real}
    (ht : 0 < theta) (hg : 0 < gamma) (hr : 0 ≤ rho) :
    uniformBase V n theta gamma rho ≤ uniformBase V' n theta gamma rho := by
  unfold uniformBase
  have h0 : 0 ≤ 2 / (gamma * theta * rho) := div_nonneg (by norm_num) (by positivity)
  have hn : (0 : Real) ≤ (n : Real) + 1 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVV hn) h0

/-- **A class is a class at any larger base and degrees.** -/
def PowerUniformClass.weaken {k : Nat} {V : Real} {dC dE dT : Nat}
    (C : PowerUniformClass k V dC dE dT) (hV : 1 ≤ V) {V' : Real} (hVV : V ≤ V')
    {dC' dE' dT' : Nat} (hC : dC ≤ dC') (hE : dE ≤ dE') (hT : dT ≤ dT') :
    PowerUniformClass k V' dC' dE' dT' where
  U := C.U
  mono := C.mono
  empty := C.empty
  decomp := by
    intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    refine C.decomp theta gamma ht ht1 hg hg1 N (le_trans ?_ hN) Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le hV (le_trans (by norm_num) hu2)
    calc (V * (2 / (gamma * theta))) ^ dT ≤ (V * (2 / (gamma * theta))) ^ dT' :=
          pow_le_pow_right₀ hVu hT
      _ ≤ (V' * (2 / (gamma * theta))) ^ dT' :=
          pow_le_pow_left₀ (by linarith) (mul_le_mul_of_nonneg_right hVV (by linarith)) _
  cover := by
    intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    refine (C.cover theta gamma ht ht1 hg hg1 N n Gamma hU).weaken ?_ ?_ ?_
    · intro rho hr hr1
      have h2 := uniformBase_two_le hV n ht ht1 hg hg1 hr hr1
      have hmono := uniformBase_mono_V hVV n ht hg hr.le
      calc uniformBase V n theta gamma rho ^ dC ≤ uniformBase V n theta gamma rho ^ dC' :=
            pow_le_pow_right₀ (by linarith) hC
        _ ≤ uniformBase V' n theta gamma rho ^ dC' := pow_le_pow_left₀ (by linarith) hmono _
    · intro rho hr hr1
      have h2 := uniformBase_two_le (hV.trans hVV) n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      have h2 := uniformBase_two_le hV n ht ht1 hg hg1 hr hr1
      have hmono := uniformBase_mono_V hVV n ht hg hr.le
      refine inv_anti₀ (pow_pos (by linarith) _) ?_
      calc uniformBase V n theta gamma rho ^ dE ≤ uniformBase V n theta gamma rho ^ dE' :=
            pow_le_pow_right₀ (by linarith) hE
        _ ≤ uniformBase V' n theta gamma rho ^ dE' := pow_le_pow_left₀ (by linarith) hmono _

/-! ### The step -/

end LeanProofs.GowersSzemeredi
