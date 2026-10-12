import GowersSzemeredi.Proofs18TightClassesFejerM

/-! **Two-track split classes** (Notes L.16x).

A split class carries one family exponent and one parameter degree for its
count and for its width exponent: the exponent is the reciprocal of the count
(`splitExp V a D = (splitCnt V a D)⁻¹`). The step uses the count of the lower
class for the remainder count `Qr`, the samples `S`, the piece bound `Pb`,
the divisor and the width scale, and the width exponent only for the
spectrum exponent `Eb`, the remainder exponent `Er` and the slice exponent
`Es`. A two-track class `SplitUniformClass2 k V ac Dc ae De` keeps the two
apart: count `(n+1)^ac·W^Dc` with threshold `(V·2/(γθ))^Dc`, and width
exponent `((n+1)^ae·W^De)⁻¹`. In dimension two the count is
`(n+1)^11·W^(2^41)` and the exponent `((n+1)^29·W^(2^46))⁻¹`, while the
one-track class must take `(32, 2^48)` for both.

* `split_exp_inv_le_fejer2`: the width exponent of the next class from a
  two-track class, with family exponent `sExpN2 k ac ae` and parameter degree
  `fsExpW2 k ac Dc ae De`;
* `SplitUniformClass2`, `splitUniformClass2_succ_fejer`: the step, with the
  count at `(sCountN k ac, max (fsCountW k ac Dc) (fejerStepThrDeg k Dc))`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The degrees of the width exponent -/

def sPbN2 (k ac ae : Nat) : Nat := ae * (sSN k ac + 1)
def fsPbW2 (k ac Dc ae De : Nat) : Nat :=
  ae * (fejerStepP k + fsSW k ac Dc + 1) + De * (fejerStepP k + 5)
def sLN2 (k ac ae : Nat) : Nat := sBqN k ac + (sErN k ae + ae)
def fsLW2 (k ac Dc ae De : Nat) : Nat := fsBqW k ac Dc + (fsErW k ae De + fsEbW k ae De)

/-- The family exponent of the width exponent of the next two-track class. -/
def sExpN2 (k ac ae : Nat) : Nat := 1 + sLN2 k ac ae + sPbN2 k ac ae

/-- The parameter degree of the width exponent of the next two-track class. -/
def fsExpW2 (k ac Dc ae De : Nat) : Nat :=
  fsZW k ac Dc + fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 6

/-- **The width exponent of the next class from a two-track class.** -/
theorem split_exp_inv_le_fejer2 {k ac Dc ae De : Nat} (hac : 1 ≤ ac) (hDc : 1 ≤ Dc) (hae : 1 ≤ ae)
    (hDe : 1 ≤ De) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V')
    (hpV : (p : Real) ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPiecesFejer gamma theta k
    let tS := classBudgetW (fejerThetaOne theta gamma k) k
    let gS := section16Delta (fejerThetaOne theta gamma k)
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
            (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho *
          famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
            (clsEs (splitExp V ae De) M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (splitCnt V ac Dc tS gS M)
            (tightZeta (fejerThetaOne theta gamma k / 4)) rho)
          (pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
            (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho)
          (famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
            (clsEs (splitExp V ae De) M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ ((n : Real) + 1) ^ sExpN2 k ac ae * splitW V' theta gamma rho ^ fsExpW2 k ac Dc ae De := by
  intro M tS gS e
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, hdd⟩ := split_step_basics_fejer (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hfacE, -⟩ := split_Qr_le_fejer (k := k) hae hDe hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hS, hS1, -, -⟩ := split_samples_le_fejer (k := k) hac hDc hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hb, hb1⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  obtain ⟨-, -, hd', hd1'⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  have hd : 0 < gS := hd'
  have hd1 : gS ≤ 1 := hd1'
  obtain ⟨hz0, hz1, hzi⟩ := tightZeta_fejer_inv_le_gen k hg hg1 ht ht1
  have hu0 : 0 ≤ 2 / (gamma * theta) := (div_pos two_pos (mul_pos hg ht)).le
  have hnv := classVertexNum_succ_le k
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set P := fejerStepP k with hPdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hnv0 : (0 : Real) < (classVertexNum k : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (classVertexNum k); linarith only [this]
  -- the count and the exponent controls at `ρ/8`
  have hcbGen : ∀ a D : Nat, splitCnt V a D tS gS M (rho / 8) ≤ ν ^ a * W ^ fsEbW k a D := by
    intro a D
    unfold splitCnt
    have hbase : splitW V tS gS (rho / 8) ≤ W ^ (P + 3 + 3) :=
      split_level_base_le hw2 hV0 hVw hr hrw (by norm_num) (by norm_num) hd hb hdd
    have hM10 : (0 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hd hb (by positivity : (0 : Real) < rho / 8)
    have h1 := tb_pow hM10 hM1 a
    have h2 : splitW V tS gS (rho / 8) ^ D ≤ ν ^ 0 * W ^ ((P + 3 + 3) * D) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase D
    have h12 := tb_mul hν hW1 (pow_nonneg hM10 _) (pow_nonneg hsw0 _) h1 h2
    exact h12.trans (tb_mono hν hW1 (by omega) (le_of_eq (by unfold fsEbW; rw [← hPdef]; ring)))
  have hcb1Gen : ∀ a D : Nat, 1 ≤ splitCnt V a D tS gS M (rho / 8) := by
    intro a D
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hd hd1 hb hb1 (by positivity : (0 : Real) < rho / 8)
      (by linarith only [hr1])
    have hM1' : (1 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1') (one_le_pow₀ (by linarith))
  have hcb := hcbGen ac Dc
  have hcb1 := hcb1Gen ac Dc
  have hEb0 : 0 < splitExp V ae De tS gS M (rho / 8) := by
    show 0 < (splitCnt V ae De tS gS M (rho / 8))⁻¹
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hcb1Gen ae De))
  have hEbi : (splitExp V ae De tS gS M (rho / 8))⁻¹ ≤ ν ^ ae * W ^ fsEbW k ae De := by
    show ((splitCnt V ae De tS gS M (rho / 8))⁻¹)⁻¹ ≤ _
    rw [inv_inv]; exact hcbGen ae De
  -- the remainder exponent at `ρ/8`, from the exponent track
  have hfac' : splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) ≤
      ν ^ ae * W ^ fsStepY k ae De := (le_max_left _ _).trans hfacE
  have hscale : 0 < rho / 8 / ((classVertexNum k : Real) + 1) :=
    div_pos (div_pos hr (by norm_num)) hnv0
  have hcr1 : 1 ≤ splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) := by
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 hb hb1 hscale (by
      rw [div_le_one hnv0]; have := Nat.cast_nonneg (α := Real) (classVertexNum k)
      linarith only [this, hr1])
    have hM1' : (1 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1') (one_le_pow₀ (by linarith))
  set cr := splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) with hcrdef
  have hEr : clsEr (splitExp V ae De) k M tS gamma (rho / 8) =
      (cr⁻¹ / 16) ^ (classVertexNum k + 1) := by
    unfold clsEr
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  have hEr0 : 0 < clsEr (splitExp V ae De) k M tS gamma (rho / 8) := by
    rw [hEr]; exact pow_pos (div_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hcr1)) (by norm_num)) _
  have hEri : (clsEr (splitExp V ae De) k M tS gamma (rho / 8))⁻¹ ≤ ν ^ sErN k ae * W ^ fsErW k ae De := by
    rw [hEr, ← inv_pow, inv_div, div_inv_eq_mul]
    have h16 : 16 * cr ≤ ν ^ ae * W ^ (4 + fsStepY k ae De) :=
      tb_const_mul hν hw2 (by norm_num) (by norm_num) (le_trans zero_le_one hcr1) hfac'
    have h16' : 16 * cr ≤ ν ^ ae * W ^ (fsStepY k ae De + 4) := by rw [add_comm]; exact h16
    have hone : (1 : Real) ≤ ν ^ ae * W ^ (fsStepY k ae De + 4) := tb_one_le hν hW1
    calc (16 * cr) ^ (classVertexNum k + 1) ≤ (ν ^ ae * W ^ (fsStepY k ae De + 4)) ^ (classVertexNum k + 1) :=
          pow_le_pow_left₀ (by linarith) h16' _
      _ ≤ (ν ^ ae * W ^ (fsStepY k ae De + 4)) ^ (2 ^ k) := pow_le_pow_right₀ hone hnv
      _ = ν ^ sErN k ae * W ^ fsErW k ae De := by
          unfold sErN fsErW; rw [mul_pow, ← pow_mul, ← pow_mul]
  -- the divisor, from the count track
  set q := ⌊splitCnt V ac Dc tS gS M (rho / 8)⌋₊ with hqdef
  have hq : (q : Real) ≤ ν ^ ac * W ^ fsEbW k ac Dc :=
    (Nat.floor_le (le_trans zero_le_one hcb1)).trans hcb
  have hq1 : ((q + 1 : Nat) : Real) ≤ ν ^ ac * W ^ (fsEbW k ac Dc + 1) := by
    push_cast; exact tb_add_one hν hw2 hq
  have hBq : familyWidthDivisor k p q ≤ ν ^ sBqN k ac * W ^ fsBqW k ac Dc := by
    unfold familyWidthDivisor
    have hpow : (((q + 1) ^ (2 * 2 ^ (k + 1)) : Nat) : Real) ≤
        ν ^ (ac * 2 ^ (k + 2)) * W ^ ((fsEbW k ac Dc + 1) * 2 ^ (k + 2)) := by
      rw [Nat.cast_pow, show 2 * 2 ^ (k + 1) = 2 ^ (k + 2) by rw [pow_succ 2 (k + 1)]; ring]
      exact tb_pow (Nat.cast_nonneg _) hq1 _
    have hpw : ((p : Nat) : Real) ≤ ν ^ 0 * W ^ 1 := by
      rw [pow_zero, one_mul, pow_one]; exact hpV.trans hV'w
    have h1 := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hpw hpow
    rw [← Nat.cast_mul] at h1
    have h2 := tb_const_mul (c := (2 : Real)) (j := 1) hν hw2 (by norm_num) (by norm_num)
      (Nat.cast_nonneg _) h1
    have h3 := tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (by positivity) h2
    push_cast at h3 ⊢
    refine h3.trans (tb_mono hν hW1 (by unfold sBqN; omega) ?_)
    unfold fsBqW
    omega
  have hBq0 : 0 < familyWidthDivisor k p q := familyWidthDivisor_pos hp q
  -- the line exponent
  set L := pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
    (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho with hLdef
  have hL0 : 0 < L := by
    rw [hLdef]; unfold pieceLineExponent
    exact div_pos (mul_pos hEr0 hEb0) hBq0
  have hLi : L⁻¹ ≤ ν ^ sLN2 k ac ae * W ^ fsLW2 k ac Dc ae De := by
    rw [hLdef]; unfold pieceLineExponent
    rw [inv_div, div_eq_mul_inv, mul_inv, ← hqdef]
    have h1 := tb_mul hν hW1 (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le hEri hEbi
    exact tb_mul hν hW1 hBq0.le (by positivity) hBq h1
  -- the slice exponent: samples from the count track, slices from the exponent track
  set S := famPieceSamples (clsQr (splitCnt V ac Dc) k M tS gamma) M rho with hSdef
  have hPbE : splitCnt V ae De tS gamma (M * S) (rho / 4) ≤ ν ^ sPbN2 k ac ae * W ^ fsPbW2 k ac Dc ae De := by
    have hMS : ((M * S : Nat) : Real) + 1 ≤ ν ^ (1 + sSN k ac) * W ^ (P + fsSW k ac Dc + 1) := by
      have h := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hS
      rw [← Nat.cast_mul] at h
      exact tb_add_one hν hw2 h
    have hbase : splitW V tS gamma (rho / 4) ≤ W ^ (P + 2 + 3) :=
      split_level_base_le hw2 hV0 hVw hr hrw (by norm_num) (by norm_num) hg hb hgd
    have hMS0 : (0 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (M * S); linarith
    have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hg hb (by positivity : (0 : Real) < rho / 4)
    unfold splitCnt
    have h1 := tb_pow hMS0 hMS ae
    have h2 : splitW V tS gamma (rho / 4) ^ De ≤ ν ^ 0 * W ^ ((P + 2 + 3) * De) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase De
    have h12 := tb_mul hν hW1 (pow_nonneg hMS0 _) (pow_nonneg hsw0 _) h1 h2
    push_cast at h12 ⊢
    refine h12.trans (tb_mono hν hW1 (le_of_eq (by unfold sPbN2; ring))
      (le_of_eq (by unfold fsPbW2; rw [← hPdef]; ring)))
  have hPbE1 : 1 ≤ splitCnt V ae De tS gamma (M * S) (rho / 4) := by
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 hb hb1
      (by positivity : (0 : Real) < rho / 4) (by linarith only [hr1])
    have hMS1 : (1 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (M * S); linarith
    push_cast at hMS1 ⊢
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hMS1) (one_le_pow₀ (by linarith))
  set Sl := famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
    (clsEs (splitExp V ae De) M tS gamma) M rho with hSldef
  have hSlval : Sl = (splitCnt V ae De tS gamma (M * S) (rho / 4))⁻¹ := by
    rw [hSldef]
    unfold famPieceSliceExponent clsEs
    rw [← hSdef, abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    rfl
  have hSl0 : 0 < Sl := by rw [hSlval]; exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hPbE1)
  have hSl1 : Sl ≤ 1 := by rw [hSlval]; exact inv_le_one_of_one_le₀ hPbE1
  have hSli : Sl⁻¹ ≤ ν ^ sPbN2 k ac ae * W ^ fsPbW2 k ac Dc ae De := by
    rw [hSlval, inv_inv]; exact hPbE
  -- the width scale, from the count track
  have hA1 : 1 ≤ familyWidthPrefactor K q := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((K * (q + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  have hA : familyWidthPrefactor K q ≤ ν ^ ac * W ^ (2 + (1 + (fsEbW k ac Dc + 1))) := by
    unfold familyWidthPrefactor
    have hKw : ((K : Nat) : Real) ≤ ν ^ 0 * W ^ 1 := by
      rw [pow_zero, one_mul, pow_one]; exact hKV.trans hV'w
    have h1 := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hKw hq1
    rw [← Nat.cast_mul, zero_add] at h1
    exact tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (Nat.cast_nonneg _) h1
  set z := pieceWidthScale (familyWidthPrefactor K) (splitCnt V ac Dc tS gS M)
    (tightZeta (fejerThetaOne theta gamma k / 4)) rho with hzdef
  have hzval : z = tightZeta (fejerThetaOne theta gamma k / 4) / familyWidthPrefactor K q := by rw [hzdef]; rfl
  have hzpos : 0 < z := by rw [hzval]; exact div_pos hz0 (lt_of_lt_of_le zero_lt_one hA1)
  have hzle : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact hz1.trans hA1
  set Λ := (ac : Real) * ν + ((fsEbW k ac Dc + 4 : Nat) : Real) * W + W ^ fejerStepT k with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  have hzinv : z⁻¹ ≤ Real.exp Λ := by
    rw [hzval, inv_div, div_eq_mul_inv]
    have hAexp : familyWidthPrefactor K q ≤ Real.exp ((ac : Real) * ν + ((fsEbW k ac Dc + 4 : Nat) : Real) * W) := by
      have h1 : ν ^ ac ≤ Real.exp ((ac : Real) * ν) := pow_le_exp_mul (by linarith) ac
      have h2 : W ^ (fsEbW k ac Dc + 4) ≤ Real.exp (((fsEbW k ac Dc + 4 : Nat) : Real) * W) :=
        pow_le_exp_mul (by linarith) _
      rw [Real.exp_add]
      refine hA.trans ?_
      rw [show 2 + (1 + (fsEbW k ac Dc + 1)) = fsEbW k ac Dc + 4 by ring]
      exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    have hze : (tightZeta (fejerThetaOne theta gamma k / 4))⁻¹ ≤ Real.exp (W ^ fejerStepT k) :=
      hzi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hu0 huw _))
    rw [hΛdef, Real.exp_add]
    exact mul_le_mul hAexp hze (inv_pos.mpr hz0).le (Real.exp_pos _).le
  have hΛle : Λ ≤ ν * W ^ fsZW k ac Dc := by
    rw [hΛdef]
    have hZ : fsZW k ac Dc = fejerStepT k + ac + fsEbW k ac Dc + 7 := rfl
    set X := W ^ (fejerStepT k + ac + fsEbW k ac Dc + 5) with hXdef
    have hX0 : 0 ≤ X := pow_nonneg hW0 _
    have hνX : X ≤ ν * X := le_mul_of_one_le_left hX0 hν
    have hν0 : 0 ≤ ν := le_trans zero_le_one hν
    have h1 : (ac : Real) * ν ≤ ν * X := by
      have ha' := nat_le_two_pow_real ac hw2
      have hle : W ^ ac ≤ X := pow_le_pow_right₀ hW1 (by omega)
      calc (ac : Real) * ν ≤ W ^ ac * ν := mul_le_mul_of_nonneg_right ha' hν0
        _ ≤ X * ν := mul_le_mul_of_nonneg_right hle hν0
        _ = ν * X := mul_comm _ _
    have h2 : ((fsEbW k ac Dc + 4 : Nat) : Real) * W ≤ ν * X := by
      have hc := nat_le_two_pow_real (fsEbW k ac Dc + 4) hw2
      have hle : W ^ (fsEbW k ac Dc + 4) * W ≤ X := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hW1 (by omega)
      calc ((fsEbW k ac Dc + 4 : Nat) : Real) * W ≤ W ^ (fsEbW k ac Dc + 4) * W :=
            mul_le_mul_of_nonneg_right hc hW0
        _ ≤ X := hle
        _ ≤ ν * X := hνX
    have h3 : W ^ fejerStepT k ≤ ν * X := by
      have hle : W ^ fejerStepT k ≤ X := pow_le_pow_right₀ hW1 (by omega)
      exact hle.trans hνX
    have h3W : (3 : Real) ≤ W ^ 2 := by nlinarith only [hw2]
    have hpos : 0 ≤ ν * X := mul_nonneg hν0 hX0
    rw [hZ, show fejerStepT k + ac + fsEbW k ac Dc + 7 = (fejerStepT k + ac + fsEbW k ac Dc + 5) + 2 by ring, pow_add,
      ← hXdef]
    calc (ac : Real) * ν + ((fsEbW k ac Dc + 4 : Nat) : Real) * W + W ^ fejerStepT k ≤ 3 * (ν * X) := by
          linarith
      _ ≤ W ^ 2 * (ν * X) := mul_le_mul_of_nonneg_right h3W hpos
      _ = ν * (X * W ^ 2) := by ring
  -- the cap
  set R := ν ^ (sLN2 k ac ae + sPbN2 k ac ae) *
    W ^ (fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 2) with hRdef
  have hR1 : 1 ≤ R := tb_one_le hν hW1
  have hLR : L⁻¹ ≤ R := hLi.trans (tb_mono hν hW1 (by omega) (by omega))
  have hLSR : (L * Sl / 4)⁻¹ ≤ R := by
    rw [show (L * Sl / 4)⁻¹ = 4 * (L⁻¹ * Sl⁻¹) by field_simp]
    have h := tb_mul hν hW1 (inv_pos.mpr hL0).le (inv_pos.mpr hSl0).le hLi hSli
    have h4 := tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (mul_nonneg (inv_pos.mpr hL0).le (inv_pos.mpr hSl0).le) h
    exact h4.trans (tb_mono hν hW1 le_rfl (by omega))
  have hcap := capped_rounded_inv_le_real hL0 hSl0 hSl1 hzpos hzle hΛ0 hzinv hR1 hLR hLSR
  refine ⟨section16CappedWidthExponent_pos (div_pos (mul_pos hL0 hSl0) (by norm_num)), ?_⟩
  refine hcap.trans ?_
  have hW4 : (14 : Real) ≤ W ^ 4 := by
    calc (14 : Real) ≤ 2 ^ 4 := by norm_num
      _ ≤ W ^ 4 := pow_le_pow_left₀ (by norm_num) hw2 4
  have hνW : 1 ≤ ν * W ^ fsZW k ac Dc := one_le_mul_of_one_le_of_one_le hν (one_le_pow₀ hW1)
  have hfront : 2 * (6 + Λ) ≤ ν * W ^ (fsZW k ac Dc + 4) := by
    rw [pow_add]
    have : 2 * (6 + Λ) ≤ 14 * (ν * W ^ fsZW k ac Dc) := by linarith
    calc 2 * (6 + Λ) ≤ 14 * (ν * W ^ fsZW k ac Dc) := this
      _ ≤ W ^ 4 * (ν * W ^ fsZW k ac Dc) := mul_le_mul_of_nonneg_right hW4 (le_trans zero_le_one hνW)
      _ = ν * (W ^ fsZW k ac Dc * W ^ 4) := by ring
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  calc 2 * ((6 + Λ) * R) = (2 * (6 + Λ)) * R := by ring
    _ ≤ (ν * W ^ (fsZW k ac Dc + 4)) * R := mul_le_mul_of_nonneg_right hfront hR0
    _ = ν ^ (1 + (sLN2 k ac ae + sPbN2 k ac ae)) *
          W ^ ((fsZW k ac Dc + 4) + (fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 2)) := by
        rw [hRdef]; ring
    _ ≤ ν ^ sExpN2 k ac ae * W ^ fsExpW2 k ac Dc ae De :=
        tb_mono hν hW1 (by unfold sExpN2; omega) (by unfold fsExpW2; omega)

end LeanProofs.GowersSzemeredi
