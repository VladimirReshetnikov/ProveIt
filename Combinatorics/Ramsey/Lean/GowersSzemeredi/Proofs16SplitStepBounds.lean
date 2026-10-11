import GowersSzemeredi.Proofs16SplitUniformClass

/-! Two-base calculus for the split step (Notes L.7, F2).

The step of route (II) is bounded in two bases: the family size `ν = n + 1`
and the parameter base `W = splitW V′ θ γ ρ`. One point is essential. The
Bohr radius `ζ = 2^(-s)` enters the width exponent only through
`log ζ⁻¹ ≤ W^T`. The capped exponent turns that into a factor `W^T`, not
`(νW)^T`. So the family exponent of the next class never sees `T`, and its
logarithm stays `O(2^k)`.

* `capped_rounded_inv_le_real`: if `z⁻¹ ≤ exp Λ` and `L⁻¹, (LS/4)⁻¹ ≤ R`
  with `R ≥ 1`, then the capped rounded exponent has inverse at most
  `2·(6 + Λ)·R`. This is the single-base `capped_rounded_inv_le` with the
  bases taken apart. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

theorem exp_three_ge_sixteen : (16 : Real) ≤ Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have he : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  have h1 : (2.7182818283 : Real) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
  have h2 : (16 : Real) ≤ (2.7182818283 : Real) ^ 3 := by norm_num
  linarith

theorem exp_five_ge_sixtyfour : (64 : Real) ≤ Real.exp 5 := by
  have h := Real.exp_one_gt_d9
  have he : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  have h1 : (2.7182818283 : Real) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h.le 5
  have h2 : (64 : Real) ≤ (2.7182818283 : Real) ^ 5 := by norm_num
  linarith

/-- **The capped rounded exponent, from real bounds.** -/
theorem capped_rounded_inv_le_real {L S z Λ R : Real} (hL : 0 < L) (hS : 0 < S) (hS1 : S ≤ 1)
    (hz : 0 < z) (hz1 : z ≤ 1) (hΛ : 0 ≤ Λ) (hzi : z⁻¹ ≤ Real.exp Λ)
    (hR1 : 1 ≤ R) (hLi : L⁻¹ ≤ R) (hLSi : (L * S / 4)⁻¹ ≤ R) :
    (section16CappedWidthExponent (L * S / 4) (section16RoundedPowerThreshold z L S))⁻¹ ≤
      2 * ((6 + Λ) * R) := by
  have hLS0 : 0 < L * S / 4 := by positivity
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  -- the first threshold
  have hT1 : positivePowerThreshold 16 z L ≤ Real.exp ((3 + Λ) * R) :=
    positivePowerThreshold_le_exp hz hL.le (by linarith) exp_three_ge_sixteen hzi hLi
  -- the second threshold
  have hD2 : 0 < (z / 16) ^ (S / 2) / 4 := by positivity
  have hD2i : ((z / 16) ^ (S / 2) / 4)⁻¹ ≤ Real.exp (5 + Λ) := by
    have hzz : 1 ≤ 16 / z := by rw [le_div_iff₀ hz]; linarith only [hz1]
    have hval : ((z / 16) ^ (S / 2) / 4)⁻¹ = 4 * (16 / z) ^ (S / 2) := by
      rw [inv_div, div_eq_mul_inv, ← Real.inv_rpow (by positivity), inv_div]
    rw [hval]
    have hr : (16 / z) ^ (S / 2) ≤ 16 / z := by
      calc (16 / z) ^ (S / 2) ≤ (16 / z) ^ (1 : Real) :=
            Real.rpow_le_rpow_of_exponent_le hzz (by linarith only [hS1])
        _ = 16 / z := Real.rpow_one _
    calc 4 * (16 / z) ^ (S / 2) ≤ 4 * (16 / z) := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = 64 * z⁻¹ := by ring
      _ ≤ Real.exp 5 * Real.exp Λ :=
          mul_le_mul exp_five_ge_sixtyfour hzi (inv_pos.mpr hz).le (Real.exp_pos _).le
      _ = Real.exp (5 + Λ) := (Real.exp_add _ _).symm
  have hT2 : positivePowerThreshold 1 ((z / 16) ^ (S / 2) / 4) (L * S / 2 - L * S / 4) ≤
      Real.exp ((0 + (5 + Λ)) * R) := by
    have he : L * S / 2 - L * S / 4 = L * S / 4 := by ring
    rw [he]
    exact positivePowerThreshold_le_exp hD2 hLS0.le (by linarith) (by simp) hD2i hLSi
  have hT : section16RoundedPowerThreshold z L S ≤ Real.exp ((5 + Λ) * R) := by
    unfold section16RoundedPowerThreshold section16RoundedExponentThreshold
    apply max_le
    · refine hT1.trans (Real.exp_le_exp.mpr ?_)
      exact mul_le_mul_of_nonneg_right (by linarith) hR0
    · refine hT2.trans (Real.exp_le_exp.mpr (le_of_eq ?_))
      ring
  -- the cap
  have hlog2 : (1 : Real) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith only [this]
  have hl21 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith only [this]
  set Tr := section16RoundedPowerThreshold z L S with hTr
  have hprod0 : 0 ≤ (5 + Λ) * R := mul_nonneg (by linarith) hR0
  have hlogT : Real.log (max 2 Tr) ≤ Real.log 2 + (5 + Λ) * R := by
    rcases le_total 2 Tr with h | h
    · rw [max_eq_right h]
      have hTpos : 0 < Tr := lt_of_lt_of_le (by norm_num) h
      have h1 : Real.log Tr ≤ (5 + Λ) * R := (Real.log_le_iff_le_exp hTpos).mpr hT
      linarith
    · rw [max_eq_left h]
      linarith
  unfold section16CappedWidthExponent
  rcases min_choice (L * S / 4) (Real.log 2 / Real.log (max 2 Tr)) with h | h
  · rw [h]
    have h6 : R ≤ 2 * ((6 + Λ) * R) := by nlinarith
    exact hLSi.trans h6
  · rw [h, inv_div]
    have hl2pos : 0 < Real.log 2 := by linarith
    rw [div_le_iff₀ hl2pos]
    nlinarith


/-! ### Two-base bookkeeping -/

theorem tb_mul {ν W x y : Real} {a1 b1 a2 b2 : Nat} (hν : 1 ≤ ν) (hW : 1 ≤ W) (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) (hx : x ≤ ν ^ a1 * W ^ b1) (hy : y ≤ ν ^ a2 * W ^ b2) :
    x * y ≤ ν ^ (a1 + a2) * W ^ (b1 + b2) := by
  have h := mul_le_mul hx hy hy0 (by positivity)
  refine h.trans (le_of_eq ?_)
  rw [pow_add, pow_add]; ring

theorem tb_pow {ν W x : Real} {a b : Nat} (hx0 : 0 ≤ x) (hx : x ≤ ν ^ a * W ^ b) (m : Nat) :
    x ^ m ≤ ν ^ (a * m) * W ^ (b * m) := by
  have h := pow_le_pow_left₀ hx0 hx m
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, pow_mul, pow_mul]

theorem tb_mono {ν W : Real} {a b a' b' : Nat} (hν : 1 ≤ ν) (hW : 1 ≤ W) (ha : a ≤ a')
    (hb : b ≤ b') : ν ^ a * W ^ b ≤ ν ^ a' * W ^ b' :=
  mul_le_mul (pow_le_pow_right₀ hν ha) (pow_le_pow_right₀ hW hb) (by positivity) (by positivity)

theorem tb_one_le {ν W : Real} {a b : Nat} (hν : 1 ≤ ν) (hW : 1 ≤ W) : 1 ≤ ν ^ a * W ^ b :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ hν) (one_le_pow₀ hW)

theorem tb_add_one {ν W x : Real} {a b : Nat} (hν : 1 ≤ ν) (hW : 2 ≤ W) (hx : x ≤ ν ^ a * W ^ b) :
    x + 1 ≤ ν ^ a * W ^ (b + 1) := by
  have h1 := tb_one_le (a := a) (b := b) hν (by linarith : (1 : Real) ≤ W)
  have hpos : 0 ≤ ν ^ a * W ^ b := le_trans zero_le_one h1
  calc x + 1 ≤ ν ^ a * W ^ b + ν ^ a * W ^ b := by linarith
    _ = 2 * (ν ^ a * W ^ b) := by ring
    _ ≤ W * (ν ^ a * W ^ b) := mul_le_mul_of_nonneg_right hW hpos
    _ = ν ^ a * W ^ (b + 1) := by rw [pow_succ]; ring

theorem tb_const_mul {ν W c x : Real} {a b j : Nat} (hν : 1 ≤ ν) (hW : 2 ≤ W) (hc0 : 0 ≤ c)
    (hc : c ≤ 2 ^ j) (hx0 : 0 ≤ x) (hx : x ≤ ν ^ a * W ^ b) : c * x ≤ ν ^ a * W ^ (j + b) := by
  have hcW : c ≤ W ^ j := hc.trans (pow_le_pow_left₀ (by norm_num) hW j)
  have h := mul_le_mul hcW hx hx0 (by positivity)
  refine h.trans (le_of_eq ?_)
  rw [pow_add]; ring

/-! ### The base of the next class -/

/-- Facts about `ν = n + 1` and `W = splitW V′ θ γ ρ`. -/
theorem split_w_facts {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V') {theta gamma rho : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho)
    (hr1 : rho ≤ 1) :
    2 ≤ splitW V' theta gamma rho ∧ 2 / (gamma * theta) ≤ splitW V' theta gamma rho ∧
      rho⁻¹ ≤ splitW V' theta gamma rho ∧ V ≤ splitW V' theta gamma rho ∧
      V' ≤ splitW V' theta gamma rho := by
  obtain ⟨h2, hu, hr', hV'⟩ := splitW_facts (hV.trans hVV) hg hg1 ht ht1 hr hr1
  exact ⟨h2, hu, hr', hVV.trans hV', hV'⟩

/-- A level-`k` split base at a scaled loss, in the base `W`. -/
theorem split_level_base_le {V W g thp rho c : Real} {j P : Nat} (hW : 2 ≤ W) (hV0 : 0 ≤ V)
    (hVW : V ≤ W) (hrho : 0 < rho) (hrW : rho⁻¹ ≤ W) (hc0 : 0 < c) (hc : c ≤ 2 ^ j)
    (hg0 : 0 < g) (hthp : 0 < thp) (hgd : 2 / (g * thp) ≤ W ^ (P + 1)) :
    splitW V thp g (rho / c) ≤ W ^ (P + j + 3) := by
  have hW0 : 0 ≤ W := by linarith
  unfold splitW
  rw [show 2 / (g * thp * (rho / c)) = 2 / (g * thp) * (rho / c)⁻¹ by field_simp]
  have hri := inv_scale_le hW hrho hrW hc0 hc
  calc V * (2 / (g * thp) * (rho / c)⁻¹) ≤ W ^ 1 * (W ^ (P + 1) * W ^ (j + 1)) := by
        rw [pow_one]
        exact mul_le_mul hVW (mul_le_mul hgd hri (by positivity) (pow_nonneg hW0 _))
          (by positivity) hW0
    _ = W ^ (P + j + 3) := by rw [← pow_add, ← pow_add]; ring_nf

theorem splitW_nonneg {V t g s : Real} (hV0 : 0 ≤ V) (hg : 0 < g) (ht : 0 < t) (hs : 0 < s) :
    0 ≤ splitW V t g s := by
  unfold splitW
  exact mul_nonneg hV0 (div_nonneg (by norm_num) (mul_pos (mul_pos hg ht) hs).le)

/-! ### The split degrees -/

def sStepY (k a D : Nat) : Nat := a * (stepP k + 1) + D * (stepP k + k + 6)
def sQrN (k a : Nat) : Nat := a * 2 ^ k
def sQrW (k a D : Nat) : Nat := sStepY k a D * 2 ^ k
def sSN (k a : Nat) : Nat := sQrN k a + 1
def sSW (k a D : Nat) : Nat := sQrW k a D + stepP k + 8
def sPbN (k a : Nat) : Nat := a * (sSN k a + 1)
def sPbW (k a D : Nat) : Nat := a * (stepP k + sSW k a D + 1) + D * (stepP k + 5)

/-- The family exponent of the count of the next class. -/
def sCountN (k a : Nat) : Nat := 1 + 2 * sSN k a + 2 * sPbN k a

/-- The parameter degree of the count of the next class. -/
def sCountW (k a D : Nat) : Nat := stepP k + 1 + 2 * sSW k a D + 2 * sPbW k a D

/-! ### Shared facts of the step -/

/-- The piece count `M = n·m` and the level-`k` bases, in the two bases. -/
theorem split_step_basics {k : Nat} {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let ν : Real := (n : Real) + 1
    let W := splitW V' theta gamma rho
    (((n * classPieces gamma theta k : Nat) : Real) ≤ ν ^ 1 * W ^ (stepP k)) ∧
      (((n * classPieces gamma theta k : Nat) : Real) + 1 ≤ ν ^ 1 * W ^ (stepP k + 1)) ∧
      (2 / (gamma * classBudget theta gamma k) ≤ W ^ (stepP k + 1)) ∧
      (2 / (classDelta theta gamma k * classBudget theta gamma k) ≤ W ^ (stepP k + 1)) := by
  intro ν W
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hm := classPieces_le_stepP k hg hg1 ht ht1
  have hgd := twoDiv_gamma_le k hg hg1 ht ht1
  have hdd := twoDiv_delta_le k hg hg1 ht ht1
  have hu0 : 0 ≤ 2 / (gamma * theta) := by linarith
  have lift : ∀ (x : Real) (j : Nat), x ≤ (2 / (gamma * theta)) ^ j → x ≤ W ^ j :=
    fun x j h => h.trans (pow_le_pow_left₀ hu0 huw j)
  have hmW := lift _ _ hm
  have hn : (n : Real) ≤ ν := by show (n : Real) ≤ (n : Real) + 1; linarith
  have hν : 1 ≤ ν := by show (1 : Real) ≤ (n : Real) + 1; have := Nat.cast_nonneg (α := Real) n; linarith
  have hM : ((n * classPieces gamma theta k : Nat) : Real) ≤ ν ^ 1 * W ^ (stepP k) := by
    rw [Nat.cast_mul, pow_one]
    exact mul_le_mul hn hmW (Nat.cast_nonneg _) (le_trans zero_le_one hν)
  exact ⟨hM, tb_add_one hν hw2 hM, lift _ _ hgd, lift _ _ hdd⟩

/-! ### The remainder count, the samples and the slices -/

/-- The count control of a split class, as a named function. -/
def splitCnt (V : Real) (a D : Nat) : Real → Real → Nat → Real → Real :=
  fun th ga n r => ((n : Real) + 1) ^ a * splitW V th ga r ^ D

/-- The width-exponent control of a split class, as a named function. -/
def splitExp (V : Real) (a D : Nat) : Real → Real → Nat → Real → Real :=
  fun th ga n r => (((n : Real) + 1) ^ a * splitW V th ga r ^ D)⁻¹

/-- **The remainder count, in two bases.** -/
theorem split_Qr_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (splitCnt V a D (classBudget theta gamma k) gamma (n * classPieces gamma theta k)
        (rho / 8 / ((classVertexNum k : Real) + 1)))
      (((3 ^ (k + 1) * (n * classPieces gamma theta k)) : Nat) : Real) ≤
      ((n : Real) + 1) ^ a * splitW V' theta gamma rho ^ sStepY k a D ∧
    clsQr (splitCnt V a D) k (n * classPieces gamma theta k) (classBudget theta gamma k) gamma
      (rho / 8) ≤ ((n : Real) + 1) ^ sQrN k a * splitW V' theta gamma rho ^ sQrW k a D := by
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, -⟩ := split_step_basics (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hb, -⟩ := classBudget_pos_le k ht ht1 hg hg1
  have hPk := stepP_ge k
  have hnv := classVertexNum_succ_le k
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set M := n * classPieces gamma theta k with hMdef
  set tS := classBudget theta gamma k
  set P := stepP k with hPdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hnv0 : (0 : Real) < (classVertexNum k : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (classVertexNum k); linarith only [this]
  have h3k : (((3 ^ (k + 1) * M) : Nat) : Real) ≤ ν ^ 1 * W ^ (2 * (k + 1) + P) := by
    rw [Nat.cast_mul]
    have h3 : ((3 ^ (k + 1) : Nat) : Real) ≤ W ^ (2 * (k + 1)) := by
      push_cast; rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith only [hw2]) _
    have h := mul_le_mul h3 hM (Nat.cast_nonneg _) (pow_nonneg hW0 _)
    refine h.trans (le_of_eq ?_)
    rw [pow_add]; ring
  have hfac : max (splitCnt V a D tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)))
        (((3 ^ (k + 1) * M) : Nat) : Real) ≤ ν ^ a * W ^ sStepY k a D := by
    unfold splitCnt
    have hc : (8 : Real) * ((classVertexNum k : Real) + 1) ≤ 2 ^ (k + 3) := by
      have h1 : ((classVertexNum k : Real) + 1) ≤ 2 ^ k := by exact_mod_cast hnv
      have h2 : (2 : Real) ^ (k + 3) = 2 ^ k * 8 := by rw [pow_add]; norm_num
      rw [h2]; linarith only [h1]
    have hbase : splitW V tS gamma (rho / (8 * ((classVertexNum k : Real) + 1))) ≤
        W ^ (P + (k + 3) + 3) :=
      split_level_base_le hw2 hV0 hVw hr hrw (mul_pos (by norm_num) hnv0) hc hg hb hgd
    rw [← div_div] at hbase
    have hscale : 0 < rho / 8 / ((classVertexNum k : Real) + 1) :=
      div_pos (div_pos hr (by norm_num)) hnv0
    have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hg hb hscale
    have hM10 : (0 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    have h1 := tb_pow hM10 hM1 a
    have h2 : splitW V tS gamma (rho / 8 / ((classVertexNum k : Real) + 1)) ^ D ≤
        ν ^ 0 * W ^ ((P + (k + 3) + 3) * D) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase D
    have h12 := tb_mul hν hW1 (pow_nonneg hM10 _) (pow_nonneg hsw0 _) h1 h2
    refine max_le (h12.trans (tb_mono hν hW1 (by omega)
      (le_of_eq (by unfold sStepY; rw [← hPdef]; ring)))) ?_
    refine h3k.trans (tb_mono hν hW1 (by omega) ?_)
    have h1' : P + 1 ≤ a * (P + 1) := Nat.le_mul_of_pos_left _ ha
    have h2' : P + k + 6 ≤ D * (P + k + 6) := Nat.le_mul_of_pos_left _ hD
    unfold sStepY
    rw [← hPdef]
    omega
  refine ⟨hfac, ?_⟩
  unfold clsQr
  have hfac1 : (1 : Real) ≤ ν ^ a * W ^ sStepY k a D := tb_one_le hν hW1
  refine (Finset.prod_le_prod (g := fun _ => ν ^ a * W ^ sStepY k a D)
    (fun i _ => le_max_of_le_right (Nat.cast_nonneg _)) (fun i _ => hfac)).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine (pow_le_pow_right₀ hfac1 hnv).trans (le_of_eq ?_)
  unfold sQrN sQrW
  rw [mul_pow, ← pow_mul, ← pow_mul]

/-- **The sample count and the slice count, in two bases.** -/
theorem split_samples_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPieces gamma theta k
    let S := famPieceSamples (clsQr (splitCnt V a D) k M (classBudget theta gamma k) gamma) M rho
    (S : Real) ≤ ((n : Real) + 1) ^ sSN k a * splitW V' theta gamma rho ^ sSW k a D ∧
      1 ≤ (S : Real) ∧
      splitCnt V a D (classBudget theta gamma k) gamma (M * S) (rho / 4) ≤
        ((n : Real) + 1) ^ sPbN k a * splitW V' theta gamma rho ^ sPbW k a D ∧
      1 ≤ splitCnt V a D (classBudget theta gamma k) gamma (M * S) (rho / 4) := by
  intro M S
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, -⟩ := split_step_basics (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hb, hb1⟩ := classBudget_pos_le k ht ht1 hg hg1
  obtain ⟨-, hQr⟩ := split_Qr_le (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set tS := classBudget theta gamma k
  set P := stepP k with hPdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hV0 : 0 ≤ V := by linarith
  -- the samples
  have hS : (S : Real) ≤ ν ^ sSN k a * W ^ sSW k a D := by
    show ((famPieceSamples (clsQr (splitCnt V a D) k M tS gamma) M rho : Nat) : Real) ≤ _
    unfold famPieceSamples
    set Q := clsQr (splitCnt V a D) k M tS gamma
    have hQ1 : max 1 (Q (rho / 8)) ≤ ν ^ sQrN k a * W ^ sQrW k a D :=
      max_le (tb_one_le hν hW1) hQr
    have hM1' : ((max 1 M : Nat) : Real) ≤ ν ^ 1 * W ^ P := by
      rcases le_total 1 M with h | h
      · rw [max_eq_right h]; exact hM
      · rw [max_eq_left h]; exact_mod_cast tb_one_le hν hW1
    have hx0 : 0 ≤ 6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) := by
      have : (0 : Real) ≤ max 1 (Q (rho / 8)) := le_trans zero_le_one (le_max_left _ _)
      positivity
    have hval : 6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) =
        24 * (max 1 (Q (rho / 8)) * (((max 1 M : Nat) : Real) * rho⁻¹)) := by
      field_simp; ring
    have hinner : max 1 (Q (rho / 8)) * (((max 1 M : Nat) : Real) * rho⁻¹) ≤
        ν ^ (sQrN k a + 1) * W ^ (sQrW k a D + (P + 1)) := by
      have hr' : rho⁻¹ ≤ ν ^ 0 * W ^ 1 := by rw [pow_zero, one_mul, pow_one]; exact hrw
      have h1 := tb_mul hν hW1 (by positivity) (inv_pos.mpr hr).le hM1' hr'
      exact tb_mul hν hW1 (le_trans zero_le_one (le_max_left _ _)) (by positivity) hQ1 h1
    have hx : 6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) ≤
        ν ^ (sQrN k a + 1) * W ^ (5 + (sQrW k a D + (P + 1))) := by
      rw [hval]
      exact tb_const_mul hν hw2 (by norm_num) (by norm_num) (by positivity) hinner
    have hceil := Nat.ceil_lt_add_one hx0
    have h2 := tb_add_one hν hw2 hx
    calc ((⌈6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4)⌉₊ : Nat) : Real)
        ≤ 6 * max 1 (Q (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) + 1 := hceil.le
      _ ≤ ν ^ (sQrN k a + 1) * W ^ (5 + (sQrW k a D + (P + 1)) + 1) := h2
      _ ≤ ν ^ sSN k a * W ^ sSW k a D := tb_mono hν hW1 (by unfold sSN; omega)
          (by unfold sSW; rw [← hPdef]; omega)
  have hS1 : (1 : Real) ≤ (S : Real) := by
    have h0 : 0 < S := famPieceSamples_pos (Qr := clsQr (splitCnt V a D) k M tS gamma) (n := M) hr
    exact Nat.one_le_cast.mpr h0
  -- the slice count
  have hMS : ((M * S : Nat) : Real) + 1 ≤ ν ^ (1 + sSN k a) * W ^ (P + sSW k a D + 1) := by
    have h := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hS
    rw [← Nat.cast_mul] at h
    exact tb_add_one hν hw2 h
  have hbase : splitW V tS gamma (rho / 4) ≤ W ^ (P + 2 + 3) :=
    split_level_base_le hw2 hV0 hVw hr hrw (by norm_num) (by norm_num) hg hb hgd
  have hMS0 : (0 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (M * S); linarith
  have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hg hb (by positivity : (0 : Real) < rho / 4)
  refine ⟨hS, hS1, ?_, ?_⟩
  · unfold splitCnt
    have h1 := tb_pow hMS0 hMS a
    have h2 : splitW V tS gamma (rho / 4) ^ D ≤ ν ^ 0 * W ^ ((P + 2 + 3) * D) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase D
    have h12 := tb_mul hν hW1 (pow_nonneg hMS0 _) (pow_nonneg hsw0 _) h1 h2
    push_cast at h12 ⊢
    refine h12.trans (tb_mono hν hW1 (le_of_eq (by unfold sPbN; ring))
      (le_of_eq (by unfold sPbW; rw [← hPdef]; ring)))
  · unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 hb hb1
      (by positivity : (0 : Real) < rho / 4) (by linarith only [hr1])
    have hMS1 : (1 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (M * S); linarith
    push_cast at hMS1 ⊢
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hMS1) (one_le_pow₀ (by linarith))

/-! ### The count -/

/-- **The count of the next class, in two bases.** -/
theorem split_count_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (famPieceGraphBound
        (clsQr (splitCnt V a D) k (n * classPieces gamma theta k) (classBudget theta gamma k) gamma)
        (clsPb (splitCnt V a D) (n * classPieces gamma theta k) (classBudget theta gamma k) gamma)
        (n * classPieces gamma theta k) rho)
      (((3 ^ (k + 1) * (n * classPieces gamma theta k)) : Nat) : Real) ≤
      ((n : Real) + 1) ^ sCountN k a * splitW V' theta gamma rho ^ sCountW k a D := by
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, -, -, -⟩ := split_step_basics (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hfac, -⟩ := split_Qr_le (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hS, hS1, hPb, hPb1⟩ := split_samples_le (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set M := n * classPieces gamma theta k with hMdef
  set tS := classBudget theta gamma k
  set S := famPieceSamples (clsQr (splitCnt V a D) k M tS gamma) M rho with hSdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hG : famPieceGraphBound (clsQr (splitCnt V a D) k M tS gamma) (clsPb (splitCnt V a D) M tS gamma)
      M rho ≤ ν ^ (1 + (2 * sSN k a + 2 * sPbN k a)) *
        W ^ (stepP k + (2 * sSW k a D + 2 * sPbW k a D)) := by
    unfold famPieceGraphBound
    rw [← hSdef]
    have hPbv : clsPb (splitCnt V a D) M tS gamma S (rho / 4) =
        splitCnt V a D tS gamma (M * S) (rho / 4) := by
      unfold clsPb; rw [abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    rw [hPbv]
    set Pb := splitCnt V a D tS gamma (M * S) (rho / 4)
    have hPb0 : 0 ≤ Pb := le_trans zero_le_one hPb1
    have hch : ((S.choose 2 : Nat) : Real) ≤ (S : Real) ^ 2 := by
      have : S.choose 2 ≤ S ^ 2 := by
        rw [Nat.choose_two_right, sq]
        exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      exact_mod_cast this
    have hmax : max Pb (((S.choose 2 : Nat) : Real) * Pb * Pb) ≤ (S : Real) ^ 2 * Pb ^ 2 := by
      refine max_le ?_ ?_
      · calc Pb ≤ Pb ^ 2 := by nlinarith only [hPb1]
          _ ≤ (S : Real) ^ 2 * Pb ^ 2 :=
              le_mul_of_one_le_left (pow_nonneg hPb0 _) (one_le_pow₀ hS1)
      · calc ((S.choose 2 : Nat) : Real) * Pb * Pb = ((S.choose 2 : Nat) : Real) * Pb ^ 2 := by ring
          _ ≤ (S : Real) ^ 2 * Pb ^ 2 := mul_le_mul_of_nonneg_right hch (pow_nonneg hPb0 _)
    have hS2 := tb_pow (by positivity) hS 2
    have hPb2 := tb_pow hPb0 hPb 2
    have h1 := tb_mul hν hW1 (by positivity) (by positivity) hS2 hPb2
    have h2 := tb_mul hν hW1 (Nat.cast_nonneg _) (by positivity) hM h1
    calc (M : Real) * max Pb (((S.choose 2 : Nat) : Real) * Pb * Pb)
        ≤ (M : Real) * ((S : Real) ^ 2 * Pb ^ 2) :=
          mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)
      _ ≤ _ := h2.trans (tb_mono hν hW1 (by omega) (by omega))
  have h3k := (le_max_right _ _).trans hfac
  refine max_le (hG.trans (tb_mono hν hW1 (by unfold sCountN; omega) (by unfold sCountW; omega))) ?_
  refine h3k.trans (tb_mono hν hW1 (by unfold sCountN sPbN; nlinarith) ?_)
  unfold sCountW sPbW sSW sQrW
  nlinarith [Nat.le_mul_of_pos_left (sStepY k a D) (Nat.two_pow_pos k)]

/-! ### The width exponent -/

def sEbW (k a D : Nat) : Nat := a * (stepP k + 1) + D * (stepP k + 6)
def sErN (k a : Nat) : Nat := a * 2 ^ k
def sErW (k a D : Nat) : Nat := (sStepY k a D + 4) * 2 ^ k
def sBqN (k a : Nat) : Nat := a * 2 ^ (k + 2)
def sBqW (k a D : Nat) : Nat := 4 + (sEbW k a D + 1) * 2 ^ (k + 2)
def sLN (k a : Nat) : Nat := sBqN k a + (sErN k a + a)
def sLW (k a D : Nat) : Nat := sBqW k a D + (sErW k a D + sEbW k a D)
def sZW (k a D : Nat) : Nat := stepT k + a + sEbW k a D + 7

/-- The family exponent of the width exponent of the next class. -/
def sExpN (k a : Nat) : Nat := 1 + sLN k a + sPbN k a

/-- The parameter degree of the width exponent of the next class. -/
def sExpW (k a D : Nat) : Nat := sZW k a D + sLW k a D + sPbW k a D + 6

theorem pow_le_exp_mul {x : Real} (hx : 0 < x) (m : Nat) : x ^ m ≤ Real.exp (m * x) := by
  rw [← Real.exp_log (pow_pos hx m)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow]
  exact mul_le_mul_of_nonneg_left ((Real.log_le_sub_one_of_pos hx).trans (by linarith))
    (Nat.cast_nonneg _)

theorem nat_le_two_pow_real (m : Nat) {W : Real} (hW : 2 ≤ W) : (m : Real) ≤ W ^ m := by
  have h : (m : Real) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  exact h.trans (pow_le_pow_left₀ (by norm_num) hW m)

/-- **The width exponent of the next class, in two bases.** -/
theorem split_exp_inv_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V')
    (hpV : (p : Real) ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPieces gamma theta k
    let tS := classBudget theta gamma k
    let gS := classDelta theta gamma k
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (splitCnt V a D tS gS M)
            (splitExp V a D tS gS M) (clsEr (splitExp V a D) k M tS gamma) rho *
          famPieceSliceExponent (clsQr (splitCnt V a D) k M tS gamma)
            (clsEs (splitExp V a D) M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (splitCnt V a D tS gS M)
            (section16Zeta theta gamma k) rho)
          (pieceLineExponent (familyWidthDivisor k p) (splitCnt V a D tS gS M)
            (splitExp V a D tS gS M) (clsEr (splitExp V a D) k M tS gamma) rho)
          (famPieceSliceExponent (clsQr (splitCnt V a D) k M tS gamma)
            (clsEs (splitExp V a D) M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ ((n : Real) + 1) ^ sExpN k a * splitW V' theta gamma rho ^ sExpW k a D := by
  intro M tS gS e
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, hdd⟩ := split_step_basics (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hfac, -⟩ := split_Qr_le (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨-, -, hPb, hPb1⟩ := split_samples_le (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hb, hb1⟩ := classBudget_pos_le k ht ht1 hg hg1
  obtain ⟨-, -, hd', hd1'⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  have hd : 0 < gS := hd'
  have hd1 : gS ≤ 1 := hd1'
  obtain ⟨hz0, hz1, hzi⟩ := section16Zeta_inv_le_gen k hg ht
  have hu0 : 0 ≤ 2 / (gamma * theta) := (div_pos two_pos (mul_pos hg ht)).le
  have hnv := classVertexNum_succ_le k
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set P := stepP k with hPdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hnv0 : (0 : Real) < (classVertexNum k : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (classVertexNum k); linarith only [this]
  -- the spectrum exponent at `ρ/8`
  have hcb : splitCnt V a D tS gS M (rho / 8) ≤ ν ^ a * W ^ sEbW k a D := by
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
    exact h12.trans (tb_mono hν hW1 (by omega) (le_of_eq (by unfold sEbW; rw [← hPdef]; ring)))
  have hcb1 : 1 ≤ splitCnt V a D tS gS M (rho / 8) := by
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hd hd1 hb hb1 (by positivity : (0 : Real) < rho / 8)
      (by linarith only [hr1])
    have hM1' : (1 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1') (one_le_pow₀ (by linarith))
  have hEb0 : 0 < splitExp V a D tS gS M (rho / 8) := by
    show 0 < (splitCnt V a D tS gS M (rho / 8))⁻¹
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hcb1)
  have hEbi : (splitExp V a D tS gS M (rho / 8))⁻¹ ≤ ν ^ a * W ^ sEbW k a D := by
    show ((splitCnt V a D tS gS M (rho / 8))⁻¹)⁻¹ ≤ _
    rw [inv_inv]; exact hcb
  -- the remainder exponent at `ρ/8`
  have hfac' : splitCnt V a D tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) ≤
      ν ^ a * W ^ sStepY k a D := (le_max_left _ _).trans hfac
  have hscale : 0 < rho / 8 / ((classVertexNum k : Real) + 1) :=
    div_pos (div_pos hr (by norm_num)) hnv0
  have hcr1 : 1 ≤ splitCnt V a D tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) := by
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 hb hb1 hscale (by
      rw [div_le_one hnv0]; have := Nat.cast_nonneg (α := Real) (classVertexNum k)
      linarith only [this, hr1])
    have hM1' : (1 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1') (one_le_pow₀ (by linarith))
  set cr := splitCnt V a D tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) with hcrdef
  have hEr : clsEr (splitExp V a D) k M tS gamma (rho / 8) =
      (cr⁻¹ / 16) ^ (classVertexNum k + 1) := by
    unfold clsEr
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  have hEr0 : 0 < clsEr (splitExp V a D) k M tS gamma (rho / 8) := by
    rw [hEr]; exact pow_pos (div_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hcr1)) (by norm_num)) _
  have hEri : (clsEr (splitExp V a D) k M tS gamma (rho / 8))⁻¹ ≤ ν ^ sErN k a * W ^ sErW k a D := by
    rw [hEr, ← inv_pow, inv_div, div_inv_eq_mul]
    have h16 : 16 * cr ≤ ν ^ a * W ^ (4 + sStepY k a D) :=
      tb_const_mul hν hw2 (by norm_num) (by norm_num) (le_trans zero_le_one hcr1) hfac'
    have h16' : 16 * cr ≤ ν ^ a * W ^ (sStepY k a D + 4) := by rw [add_comm]; exact h16
    have hone : (1 : Real) ≤ ν ^ a * W ^ (sStepY k a D + 4) := tb_one_le hν hW1
    calc (16 * cr) ^ (classVertexNum k + 1) ≤ (ν ^ a * W ^ (sStepY k a D + 4)) ^ (classVertexNum k + 1) :=
          pow_le_pow_left₀ (by linarith) h16' _
      _ ≤ (ν ^ a * W ^ (sStepY k a D + 4)) ^ (2 ^ k) := pow_le_pow_right₀ hone hnv
      _ = ν ^ sErN k a * W ^ sErW k a D := by
          unfold sErN sErW; rw [mul_pow, ← pow_mul, ← pow_mul]
  -- the divisor
  set q := ⌊splitCnt V a D tS gS M (rho / 8)⌋₊ with hqdef
  have hq : (q : Real) ≤ ν ^ a * W ^ sEbW k a D :=
    (Nat.floor_le (le_trans zero_le_one hcb1)).trans hcb
  have hq1 : ((q + 1 : Nat) : Real) ≤ ν ^ a * W ^ (sEbW k a D + 1) := by
    push_cast; exact tb_add_one hν hw2 hq
  have hBq : familyWidthDivisor k p q ≤ ν ^ sBqN k a * W ^ sBqW k a D := by
    unfold familyWidthDivisor
    have hpow : (((q + 1) ^ (2 * 2 ^ (k + 1)) : Nat) : Real) ≤
        ν ^ (a * 2 ^ (k + 2)) * W ^ ((sEbW k a D + 1) * 2 ^ (k + 2)) := by
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
    unfold sBqW
    omega
  have hBq0 : 0 < familyWidthDivisor k p q := familyWidthDivisor_pos hp q
  -- the line exponent
  set L := pieceLineExponent (familyWidthDivisor k p) (splitCnt V a D tS gS M)
    (splitExp V a D tS gS M) (clsEr (splitExp V a D) k M tS gamma) rho with hLdef
  have hL0 : 0 < L := by
    rw [hLdef]; unfold pieceLineExponent
    exact div_pos (mul_pos hEr0 hEb0) hBq0
  have hLi : L⁻¹ ≤ ν ^ sLN k a * W ^ sLW k a D := by
    rw [hLdef]; unfold pieceLineExponent
    rw [inv_div, div_eq_mul_inv, mul_inv, ← hqdef]
    have h1 := tb_mul hν hW1 (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le hEri hEbi
    exact tb_mul hν hW1 hBq0.le (by positivity) hBq h1
  -- the slice exponent
  set S := famPieceSamples (clsQr (splitCnt V a D) k M tS gamma) M rho with hSdef
  set Sl := famPieceSliceExponent (clsQr (splitCnt V a D) k M tS gamma)
    (clsEs (splitExp V a D) M tS gamma) M rho with hSldef
  have hSlval : Sl = (splitCnt V a D tS gamma (M * S) (rho / 4))⁻¹ := by
    rw [hSldef]
    unfold famPieceSliceExponent clsEs
    rw [← hSdef, abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    rfl
  have hSl0 : 0 < Sl := by rw [hSlval]; exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hPb1)
  have hSl1 : Sl ≤ 1 := by rw [hSlval]; exact inv_le_one_of_one_le₀ hPb1
  have hSli : Sl⁻¹ ≤ ν ^ sPbN k a * W ^ sPbW k a D := by rw [hSlval, inv_inv]; exact hPb
  -- the width scale
  have hA1 : 1 ≤ familyWidthPrefactor K q := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((K * (q + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  have hA : familyWidthPrefactor K q ≤ ν ^ a * W ^ (2 + (1 + (sEbW k a D + 1))) := by
    unfold familyWidthPrefactor
    have hKw : ((K : Nat) : Real) ≤ ν ^ 0 * W ^ 1 := by
      rw [pow_zero, one_mul, pow_one]; exact hKV.trans hV'w
    have h1 := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hKw hq1
    rw [← Nat.cast_mul, zero_add] at h1
    exact tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (Nat.cast_nonneg _) h1
  set z := pieceWidthScale (familyWidthPrefactor K) (splitCnt V a D tS gS M)
    (section16Zeta theta gamma k) rho with hzdef
  have hzval : z = section16Zeta theta gamma k / familyWidthPrefactor K q := by rw [hzdef]; rfl
  have hzpos : 0 < z := by rw [hzval]; exact div_pos hz0 (lt_of_lt_of_le zero_lt_one hA1)
  have hzle : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact hz1.trans hA1
  set Λ := (a : Real) * ν + ((sEbW k a D + 4 : Nat) : Real) * W + W ^ stepT k with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  have hzinv : z⁻¹ ≤ Real.exp Λ := by
    rw [hzval, inv_div, div_eq_mul_inv]
    have hAexp : familyWidthPrefactor K q ≤ Real.exp ((a : Real) * ν + ((sEbW k a D + 4 : Nat) : Real) * W) := by
      have h1 : ν ^ a ≤ Real.exp ((a : Real) * ν) := pow_le_exp_mul (by linarith) a
      have h2 : W ^ (sEbW k a D + 4) ≤ Real.exp (((sEbW k a D + 4 : Nat) : Real) * W) :=
        pow_le_exp_mul (by linarith) _
      rw [Real.exp_add]
      refine hA.trans ?_
      rw [show 2 + (1 + (sEbW k a D + 1)) = sEbW k a D + 4 by ring]
      exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    have hze : (section16Zeta theta gamma k)⁻¹ ≤ Real.exp (W ^ stepT k) :=
      hzi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hu0 huw _))
    rw [hΛdef, Real.exp_add]
    exact mul_le_mul hAexp hze (inv_pos.mpr hz0).le (Real.exp_pos _).le
  have hΛle : Λ ≤ ν * W ^ sZW k a D := by
    rw [hΛdef]
    have hZ : sZW k a D = stepT k + a + sEbW k a D + 7 := rfl
    set X := W ^ (stepT k + a + sEbW k a D + 5) with hXdef
    have hX0 : 0 ≤ X := pow_nonneg hW0 _
    have hνX : X ≤ ν * X := le_mul_of_one_le_left hX0 hν
    have hν0 : 0 ≤ ν := le_trans zero_le_one hν
    have h1 : (a : Real) * ν ≤ ν * X := by
      have ha' := nat_le_two_pow_real a hw2
      have hle : W ^ a ≤ X := pow_le_pow_right₀ hW1 (by omega)
      calc (a : Real) * ν ≤ W ^ a * ν := mul_le_mul_of_nonneg_right ha' hν0
        _ ≤ X * ν := mul_le_mul_of_nonneg_right hle hν0
        _ = ν * X := mul_comm _ _
    have h2 : ((sEbW k a D + 4 : Nat) : Real) * W ≤ ν * X := by
      have hc := nat_le_two_pow_real (sEbW k a D + 4) hw2
      have hle : W ^ (sEbW k a D + 4) * W ≤ X := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hW1 (by omega)
      calc ((sEbW k a D + 4 : Nat) : Real) * W ≤ W ^ (sEbW k a D + 4) * W :=
            mul_le_mul_of_nonneg_right hc hW0
        _ ≤ X := hle
        _ ≤ ν * X := hνX
    have h3 : W ^ stepT k ≤ ν * X := by
      have hle : W ^ stepT k ≤ X := pow_le_pow_right₀ hW1 (by omega)
      exact hle.trans hνX
    have h3W : (3 : Real) ≤ W ^ 2 := by nlinarith only [hw2]
    have hpos : 0 ≤ ν * X := mul_nonneg hν0 hX0
    rw [hZ, show stepT k + a + sEbW k a D + 7 = (stepT k + a + sEbW k a D + 5) + 2 by ring, pow_add,
      ← hXdef]
    calc (a : Real) * ν + ((sEbW k a D + 4 : Nat) : Real) * W + W ^ stepT k ≤ 3 * (ν * X) := by
          linarith
      _ ≤ W ^ 2 * (ν * X) := mul_le_mul_of_nonneg_right h3W hpos
      _ = ν * (X * W ^ 2) := by ring
  -- the cap
  set R := ν ^ (sLN k a + sPbN k a) * W ^ (sLW k a D + sPbW k a D + 2) with hRdef
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
  have hνW : 1 ≤ ν * W ^ sZW k a D := one_le_mul_of_one_le_of_one_le hν (one_le_pow₀ hW1)
  have hfront : 2 * (6 + Λ) ≤ ν * W ^ (sZW k a D + 4) := by
    rw [pow_add]
    have : 2 * (6 + Λ) ≤ 14 * (ν * W ^ sZW k a D) := by linarith
    calc 2 * (6 + Λ) ≤ 14 * (ν * W ^ sZW k a D) := this
      _ ≤ W ^ 4 * (ν * W ^ sZW k a D) := mul_le_mul_of_nonneg_right hW4 (le_trans zero_le_one hνW)
      _ = ν * (W ^ sZW k a D * W ^ 4) := by ring
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  calc 2 * ((6 + Λ) * R) = (2 * (6 + Λ)) * R := by ring
    _ ≤ (ν * W ^ (sZW k a D + 4)) * R := mul_le_mul_of_nonneg_right hfront hR0
    _ = ν ^ (1 + (sLN k a + sPbN k a)) * W ^ ((sZW k a D + 4) + (sLW k a D + sPbW k a D + 2)) := by
        rw [hRdef]; ring
    _ ≤ ν ^ sExpN k a * W ^ sExpW k a D :=
        tb_mono hν hW1 (by unfold sExpN; omega) (by unfold sExpW; omega)

/-! ### The split step -/

/-- The family exponent of the next split class. -/
def splitStepA (k a : Nat) : Nat := sCountN k a + sExpN k a

/-- The parameter degree of the next split class. -/
def splitStepD (k a D : Nat) : Nat := sCountW k a D + sExpW k a D + stepThrDeg k D

theorem splitCnt_controls {V : Real} (hV : 1 ≤ V) (a D : Nat) :
    (∀ theta gamma n s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s → s ≤ 1 →
      1 ≤ splitCnt V a D theta gamma n s) ∧
    (∀ theta gamma n s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s → s ≤ 1 →
      0 < splitExp V a D theta gamma n s ∧ splitExp V a D theta gamma n s ≤ 1) ∧
    (∀ theta gamma s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 ≤ s →
      Monotone fun n => splitCnt V a D theta gamma n s) ∧
    (∀ theta gamma s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s →
      Antitone fun n => splitExp V a D theta gamma n s) := by
  have hcnt1 : ∀ theta gamma n s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s → s ≤ 1 →
      1 ≤ splitCnt V a D theta gamma n s := by
    intro theta gamma n s ht ht1 hg hg1 hs hs1
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hs hs1
    have hn1 : (1 : Real) ≤ (n : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) n; linarith
    unfold splitCnt
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn1) (one_le_pow₀ (by linarith))
  have hmono : ∀ theta gamma s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 ≤ s →
      Monotone fun n => splitCnt V a D theta gamma n s := by
    intro theta gamma s ht _ hg _ hs n n' hnn
    unfold splitCnt
    have hsw : 0 ≤ splitW V theta gamma s := by
      unfold splitW
      exact mul_nonneg (by linarith) (div_nonneg (by norm_num) (by positivity))
    have hnn' : ((n : Real) + 1) ≤ (n' : Real) + 1 := by
      have : (n : Real) ≤ n' := by exact_mod_cast hnn
      linarith
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hnn' a) (pow_nonneg hsw _)
  refine ⟨hcnt1, ?_, hmono, ?_⟩
  · intro theta gamma n s ht ht1 hg hg1 hs hs1
    have h1 := hcnt1 theta gamma n s ht ht1 hg hg1 hs hs1
    show 0 < (splitCnt V a D theta gamma n s)⁻¹ ∧ (splitCnt V a D theta gamma n s)⁻¹ ≤ 1
    exact ⟨inv_pos.mpr (lt_of_lt_of_le zero_lt_one h1), inv_le_one_of_one_le₀ h1⟩
  · intro theta gamma s ht ht1 hg hg1 hs n n' hnn
    show (splitCnt V a D theta gamma n' s)⁻¹ ≤ (splitCnt V a D theta gamma n s)⁻¹
    have hpos : 0 < splitCnt V a D theta gamma n s := by
      unfold splitCnt splitW
      have : (0 : Real) < (n : Real) + 1 := by positivity
      have hV0 : (0 : Real) < V := by linarith
      positivity
    exact inv_anti₀ hpos (hmono theta gamma s ht ht1 hg hg1 hs.le hnn)

/-- **The split step of route (II).** A split class of dimension `k ≥ 1`
with the family Lemma 16.6 at dimension `k` gives a split class of dimension
`k+1`, with family exponent `splitStepA k a` and parameter degree
`splitStepD k a D`. -/
theorem splitUniformClass_succ {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V) {a D : Nat}
    (ha : 1 ≤ a) (hD : 1 ≤ D) (C : SplitUniformClass k V a D) {K p : Nat} (hK : 1 ≤ K)
    (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    Nonempty (SplitUniformClass (k + 1) V' (splitStepA k a) (splitStepD k a D)) := by
  classical
  obtain ⟨hCnt, hExp, hCntMono, hExpAnti⟩ := splitCnt_controls hV a D
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (classPieces gamma theta k) → StepPiece C N theta gamma,
        Gamma ⊆ stepPieceGraphs C P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => ClassPiece.empty C _ _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V' * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le (hV.trans hVV) (le_trans (by norm_num) hu2)
    have hN' : classStepThr (fun theta gamma => (V * (2 / (gamma * theta))) ^ D) theta gamma k ≤ N := by
      rw [← classStepThreshold_eq]
      refine (step_thr_le hk hV hVV hg hg1 ht ht1).trans (le_trans ?_ hN)
      exact pow_le_pow_right₀ hVu (by unfold splitStepD; omega)
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover_gen C hk hCnt hExp hCntMono hExpAnti (familyWidthPrefactor_pos hK)
      (familyWidthDivisor_pos hp) hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      have hc := split_count_le (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      refine hc.trans (tb_mono hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepD; omega))
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith)))
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := split_exp_inv_le (k := k) ha hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      have hmono := tb_mono (a := sExpN k a) (b := sExpW k a D) (a' := splitStepA k a)
        (b' := splitStepD k a D) hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepD; omega)
      have h1 := inv_anti₀ (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith))) hmono
      have h2 := inv_anti₀ (inv_pos.mpr he0) hei
      rw [inv_inv] at h2
      exact h1.trans h2

end LeanProofs.GowersSzemeredi
