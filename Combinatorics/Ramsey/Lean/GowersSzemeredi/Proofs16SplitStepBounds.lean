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
  bases taken apart.

The step bounds are proved once at any parameter exponent `P` and Bohr
exponent `T` (`split_step_basics_W` … `split_exp_inv_le_W2`, degrees `sw…`),
with the Section 16 inputs as hypotheses and two tracks for the width
exponent. The printed bounds are their instances at `(stepP k, stepT k)` (the
width exponent on the diagonal), the Fejér ones (`Proofs16SplitStepFejer`) at
`(fejerStepP k, fejerStepT k)`.

The 17 declarations of this module that the final route does not use are in
`Proofs16SplitStepBoundsSide`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

theorem exp_three_ge_sixteen : (16 : Real) ≤ Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have he : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  have h1 : (2.7182818283 : Real) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
  linarith

theorem exp_five_ge_sixtyfour : (64 : Real) ≤ Real.exp 5 := by
  have h := Real.exp_one_gt_d9
  have he : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  have h1 : (2.7182818283 : Real) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h.le 5
  linarith

/-- **The capped rounded exponent, from real bounds.** -/
theorem capped_rounded_inv_le_real {L S z Λ R : Real} (hL : 0 < L) (hS : 0 < S) (hS1 : S ≤ 1)
    (hz : 0 < z) (hz1 : z ≤ 1) (hΛ : 0 ≤ Λ) (hzi : z⁻¹ ≤ Real.exp Λ)
    (hR1 : 1 ≤ R) (hLi : L⁻¹ ≤ R) (hLSi : (L * S / 4)⁻¹ ≤ R) :
    (section16CappedWidthExponent (L * S / 4) (section16RoundedPowerThreshold z L S))⁻¹ ≤
      2 * ((6 + Λ) * R) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  -- the coefficient of the second threshold
  have hD2i : ((z / 16) ^ (S / 2) / 4)⁻¹ ≤ Real.exp (5 + Λ) := by
    have hzz : 1 ≤ 16 / z := by rw [le_div_iff₀ hz]; linarith
    rw [inv_div, div_eq_mul_inv, ← Real.inv_rpow (by positivity), inv_div, Real.exp_add]
    calc 4 * (16 / z) ^ (S / 2) ≤ 4 * (16 / z) := by
          gcongr; exact Real.rpow_le_self_of_one_le hzz (by linarith)
      _ = 64 * z⁻¹ := by ring
      _ ≤ Real.exp 5 * Real.exp Λ := by gcongr; exact exp_five_ge_sixtyfour
  -- the two thresholds
  have hT : section16RoundedPowerThreshold z L S ≤ Real.exp ((5 + Λ) * R) := by
    rw [section16RoundedPowerThreshold, section16RoundedExponentThreshold,
      show L * S / 2 - L * S / 4 = L * S / 4 by ring]
    refine max_le ((positivePowerThreshold_le_exp hz hL.le (by linarith) exp_three_ge_sixteen hzi
      hLi).trans (Real.exp_le_exp.mpr (by nlinarith))) ?_
    exact (positivePowerThreshold_le_exp (by positivity) (by positivity) (by linarith)
      Real.exp_zero.ge hD2i hLSi).trans_eq (by rw [zero_add])
  -- the cap
  set T := section16RoundedPowerThreshold z L S
  have hlog : Real.log (max 2 T) ≤ Real.log 2 + (5 + Λ) * R := by
    have h1 := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ (5 + Λ) * R)
    rw [← Real.log_exp ((5 + Λ) * R), ← Real.log_mul two_ne_zero (Real.exp_pos _).ne']
    exact Real.log_le_log (lt_max_of_lt_left two_pos) (max_le (by linarith) (by linarith))
  have hl2 := Real.log_two_gt_d9
  unfold section16CappedWidthExponent
  rcases min_choice (L * S / 4) (Real.log 2 / Real.log (max 2 T)) with h | h <;> rw [h]
  · linarith [mul_nonneg hΛ hR0]
  · rw [inv_div, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hΛ hR0]

/-! ### Two-base bookkeeping -/

theorem tb_mul {ν W x y : Real} {a1 b1 a2 b2 : Nat} (hν : 1 ≤ ν) (hW : 1 ≤ W)
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

theorem tb_const_mul {ν W c x : Real} {a b j : Nat} (hW : 2 ≤ W)
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
theorem split_level_base_le {V W g thp rho c : Real} {j P : Nat} (hW : 2 ≤ W)
    (hVW : V ≤ W) (hrho : 0 < rho) (hrW : rho⁻¹ ≤ W) (hc0 : 0 < c) (hc : c ≤ 2 ^ j)
    (hg0 : 0 < g) (hthp : 0 < thp) (hgd : 2 / (g * thp) ≤ W ^ (P + 1)) :
    splitW V thp g (rho / c) ≤ W ^ (P + j + 3) := by
  have hW0 : 0 ≤ W := by linarith
  unfold splitW
  rw [show 2 / (g * thp * (rho / c)) = 2 / (g * thp) * (rho / c)⁻¹ by field_simp]
  have hri := inv_scale_le hW hrho hrW hc
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

def sQrN (k a : Nat) : Nat := a * 2 ^ k
def sSN (k a : Nat) : Nat := sQrN k a + 1
def sPbN (k a : Nat) : Nat := a * (sSN k a + 1)
/-- The family exponent of the count of the next class. -/
def sCountN (k a : Nat) : Nat := 1 + 2 * sSN k a + 2 * sPbN k a

/-! ### The split degrees at any `(P, T)`

The printed split degrees `s…W` are these at `(stepP k, stepT k)`, the Fejér ones
`fs…W` (`Proofs16SplitStepFejer`) at `(fejerStepP k, fejerStepT k)`, both by `rfl`;
the two-track degrees `sw…2` reduce to the one-track ones on the diagonal. -/

def swStepY (P k a D : Nat) : Nat := a * (P + 1) + D * (P + k + 6)
def swQrW (P k a D : Nat) : Nat := swStepY P k a D * 2 ^ k
def swSW (P k a D : Nat) : Nat := swQrW P k a D + P + 8
def swPbW (P k a D : Nat) : Nat := a * (P + swSW P k a D + 1) + D * (P + 5)
def swCountW (P k a D : Nat) : Nat := P + 1 + 2 * swSW P k a D + 2 * swPbW P k a D
def swEbW (P k a D : Nat) : Nat := a * (P + 1) + D * (P + 6)
def swErW (P k a D : Nat) : Nat := (swStepY P k a D + 4) * 2 ^ k
def swBqW (P k a D : Nat) : Nat := 4 + (swEbW P k a D + 1) * 2 ^ (k + 2)
def swZW (P T k a D : Nat) : Nat := T + a + swEbW P k a D + 7
def swPbW2 (P k ac Dc ae De : Nat) : Nat := ae * (P + swSW P k ac Dc + 1) + De * (P + 5)
def swLW2 (P k ac Dc ae De : Nat) : Nat := swBqW P k ac Dc + (swErW P k ae De + swEbW P k ae De)
def swExpW2 (P T k ac Dc ae De : Nat) : Nat :=
  swZW P T k ac Dc + swLW2 P k ac Dc ae De + swPbW2 P k ac Dc ae De + 6

/-! ### Shared facts of the step -/

/-- The piece count `M = n·m` and the level-`k` bases, in the two bases. -/
theorem split_step_basics_W {P m : Nat} {tS gS V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat)
    (hm : (m : Real) ≤ (2 / (gamma * theta)) ^ P) (hgd : 2 / (gamma * tS) ≤ (2 / (gamma * theta)) ^ (P + 1))
    (hdd : 2 / (gS * tS) ≤ (2 / (gamma * theta)) ^ (P + 1)) :
    let ν : Real := (n : Real) + 1
    let W := splitW V' theta gamma rho
    (((n * m : Nat) : Real) ≤ ν ^ 1 * W ^ (P)) ∧
      (((n * m : Nat) : Real) + 1 ≤ ν ^ 1 * W ^ (P + 1)) ∧
      (2 / (gamma * tS) ≤ W ^ (P + 1)) ∧
      (2 / (gS * tS) ≤ W ^ (P + 1)) := by
  intro ν W
  obtain ⟨hw2, huw, _, _, _⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hu0 : 0 ≤ 2 / (gamma * theta) := by linarith
  have lift : ∀ (x : Real) (j : Nat), x ≤ (2 / (gamma * theta)) ^ j → x ≤ W ^ j :=
    fun x j h => h.trans (pow_le_pow_left₀ hu0 huw j)
  have hmW := lift _ _ hm
  have hn : (n : Real) ≤ ν := by show (n : Real) ≤ (n : Real) + 1; linarith
  have hν : 1 ≤ ν := by show (1 : Real) ≤ (n : Real) + 1; have := Nat.cast_nonneg (α := Real) n; linarith
  have hM : ((n * m : Nat) : Real) ≤ ν ^ 1 * W ^ (P) := by
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
    have hnn' : ((n : Real) + 1) ≤ (n' : Real) + 1 := by gcongr
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
      positivity
    exact inv_anti₀ hpos (hmono theta gamma s ht ht1 hg hg1 hs.le hnn)

/-- A split count at the scaled loss `ρ/c`, `c ≤ 2^j`, in the two bases. -/
private theorem splitCnt_scaled_le {V W ν t g rho c : Real} {a D M x y j P : Nat} (hV : 0 ≤ V)
    (hW : 2 ≤ W) (hVW : V ≤ W) (hν : 1 ≤ ν) (ht : 0 < t) (hg : 0 < g) (hr : 0 < rho)
    (hrW : rho⁻¹ ≤ W) (hc0 : 0 < c) (hc : c ≤ 2 ^ j) (hgd : 2 / (g * t) ≤ W ^ (P + 1))
    (hM : (M : Real) + 1 ≤ ν ^ x * W ^ y) :
    splitCnt V a D t g M (rho / c) ≤ ν ^ (x * a) * W ^ (y * a + (P + j + 3) * D) := by
  have h0 := splitW_nonneg hV hg ht (div_pos hr hc0)
  calc splitCnt V a D t g M (rho / c) ≤ (ν ^ x * W ^ y) ^ a * (W ^ (P + j + 3)) ^ D := by
        unfold splitCnt
        gcongr
        exact split_level_base_le hW hVW hr hrW hc0 hc hg ht hgd
    _ = ν ^ (x * a) * W ^ (y * a + (P + j + 3) * D) := by ring

/-- **The remainder count, in two bases.** -/
theorem split_Qr_le_W {k a D P m : Nat} {tS gS : Real} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat)
    (hm0 : (m : Real) ≤ (2 / (gamma * theta)) ^ P)
    (hgd0 : 2 / (gamma * tS) ≤ (2 / (gamma * theta)) ^ (P + 1))
    (hdd0 : 2 / (gS * tS) ≤ (2 / (gamma * theta)) ^ (P + 1)) (hb : 0 < tS) (hPk : k + 8 ≤ P) :
    max (splitCnt V a D (tS) gamma (n * m)
        (rho / 8 / ((classVertexNum k : Real) + 1)))
      (((3 ^ (k + 1) * (n * m)) : Nat) : Real) ≤
      ((n : Real) + 1) ^ a * splitW V' theta gamma rho ^ swStepY P k a D ∧
    clsQr (splitCnt V a D) k (n * m) (tS) gamma
      (rho / 8) ≤ ((n : Real) + 1) ^ sQrN k a * splitW V' theta gamma rho ^ swQrW P k a D := by
  obtain ⟨hw2, -, hrw, hVw, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, -⟩ := split_step_basics_W hV hVV hg hg1 ht ht1 hr hr1 n hm0 hgd0 hdd0
  have hnv := classVertexNum_succ_le k
  set ν : Real := (n : Real) + 1
  set W := splitW V' theta gamma rho
  have hν : 1 ≤ ν := le_add_of_nonneg_left n.cast_nonneg
  have hW1 : 1 ≤ W := by linarith
  have hc : (8 : Real) * ((classVertexNum k : Real) + 1) ≤ 2 ^ (k + 3) := by
    have h1 : ((classVertexNum k : Real) + 1) ≤ 2 ^ k := by exact_mod_cast hnv
    rw [pow_add]; linarith
  have hfac : max (splitCnt V a D tS gamma (n * m) (rho / 8 / ((classVertexNum k : Real) + 1)))
      (((3 ^ (k + 1) * (n * m)) : Nat) : Real) ≤ ν ^ a * W ^ swStepY P k a D := by
    refine max_le ?_ ?_
    · rw [div_div]
      exact (splitCnt_scaled_le (by linarith) hw2 hVw hν hb hg hr hrw (by positivity) hc hgd
        hM1).trans_eq (by unfold swStepY; ring)
    · have h3 : ((3 ^ (k + 1) : Nat) : Real) ≤ 2 ^ (2 * (k + 1)) := by
        rw [pow_mul]; push_cast; gcongr; norm_num
      rw [Nat.cast_mul]
      refine (tb_const_mul hw2 h3 (Nat.cast_nonneg _) hM).trans (tb_mono hν hW1 ha ?_)
      have := Nat.le_mul_of_pos_left (P + 1) ha
      have := Nat.le_mul_of_pos_left (P + k + 6) hD
      unfold swStepY; omega
  refine ⟨hfac, ?_⟩
  unfold clsQr
  refine (Finset.prod_le_prod (fun i _ => le_max_of_le_right (Nat.cast_nonneg _))
    (fun i _ => hfac)).trans ?_
  rw [Fin.prod_const]
  refine (pow_le_pow_right₀ (tb_one_le hν hW1) hnv).trans_eq ?_
  unfold sQrN swQrW
  rw [mul_pow, ← pow_mul, ← pow_mul]

/-- **The sample count and the slice count, in two bases.** -/
theorem split_samples_le_W {k a D P m : Nat} {tS gS : Real} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat)
    (hm0 : (m : Real) ≤ (2 / (gamma * theta)) ^ P)
    (hgd0 : 2 / (gamma * tS) ≤ (2 / (gamma * theta)) ^ (P + 1))
    (hdd0 : 2 / (gS * tS) ≤ (2 / (gamma * theta)) ^ (P + 1)) (hb : 0 < tS) (hb1 : tS ≤ 1) (hPk : k + 8 ≤ P) :
    let M := n * m
    let S := famPieceSamples (clsQr (splitCnt V a D) k M (tS) gamma) M rho
    (S : Real) ≤ ((n : Real) + 1) ^ sSN k a * splitW V' theta gamma rho ^ swSW P k a D ∧
      1 ≤ (S : Real) ∧
      splitCnt V a D (tS) gamma (M * S) (rho / 4) ≤
        ((n : Real) + 1) ^ sPbN k a * splitW V' theta gamma rho ^ swPbW P k a D ∧
      1 ≤ splitCnt V a D (tS) gamma (M * S) (rho / 4) := by
  intro M S
  obtain ⟨hw2, -, hrw, hVw, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, -, hgd, -⟩ := split_step_basics_W hV hVV hg hg1 ht ht1 hr hr1 n hm0 hgd0 hdd0
  obtain ⟨-, hQr⟩ := split_Qr_le_W (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n hm0 hgd0 hdd0 hb hPk
  set ν : Real := (n : Real) + 1
  set W := splitW V' theta gamma rho
  have hν : 1 ≤ ν := le_add_of_nonneg_left n.cast_nonneg
  have hW1 : 1 ≤ W := by linarith
  have hS : (S : Real) ≤ ν ^ sSN k a * W ^ swSW P k a D :=
    (famPieceSamples_le_two_bases hν hw2 hr hrw hQr hM).trans
      (tb_mono hν hW1 le_rfl (by unfold swSW; omega))
  have hMS : ((M * S : Nat) : Real) + 1 ≤ ν ^ (1 + sSN k a) * W ^ (P + swSW P k a D + 1) := by
    push_cast; exact tb_add_one hν hw2 (tb_mul hν hW1 (Nat.cast_nonneg _) hM hS)
  refine ⟨hS, Nat.one_le_cast.mpr (famPieceSamples_pos hr), ?_,
    (splitCnt_controls hV a D).1 tS gamma (M * S) (rho / 4) hb hb1 hg hg1 (by positivity)
      (by linarith)⟩
  exact (splitCnt_scaled_le (by linarith) hw2 hVw hν hb hg hr hrw four_pos
    (by norm_num : (4 : Real) ≤ 2 ^ 2) hgd hMS).trans_eq (by unfold sPbN swPbW; ring)

/-! ### The count -/

/-- **The count of the next class, in two bases.** -/
theorem split_count_le_W {k a D P m : Nat} {tS gS : Real} (ha : 1 ≤ a) (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat)
    (hm0 : (m : Real) ≤ (2 / (gamma * theta)) ^ P)
    (hgd0 : 2 / (gamma * tS) ≤ (2 / (gamma * theta)) ^ (P + 1))
    (hdd0 : 2 / (gS * tS) ≤ (2 / (gamma * theta)) ^ (P + 1)) (hb : 0 < tS) (hb1 : tS ≤ 1) (hPk : k + 8 ≤ P) :
    max (famPieceGraphBound
        (clsQr (splitCnt V a D) k (n * m) (tS) gamma)
        (clsPb (splitCnt V a D) (n * m) (tS) gamma)
        (n * m) rho)
      (((3 ^ (k + 1) * (n * m)) : Nat) : Real) ≤
      ((n : Real) + 1) ^ sCountN k a * splitW V' theta gamma rho ^ swCountW P k a D := by
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, -, -, -⟩ := split_step_basics_W hV hVV hg hg1 ht ht1 hr hr1 n hm0 hgd0 hdd0
  obtain ⟨hfac, -⟩ := split_Qr_le_W (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n hm0 hgd0 hdd0 hb hPk
  obtain ⟨hS, hS1, hPb, hPb1⟩ := split_samples_le_W (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n hm0 hgd0 hdd0 hb hb1 hPk
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set M := n * m with hMdef
  set S := famPieceSamples (clsQr (splitCnt V a D) k M tS gamma) M rho with hSdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hG : famPieceGraphBound (clsQr (splitCnt V a D) k M tS gamma) (clsPb (splitCnt V a D) M tS gamma)
      M rho ≤ ν ^ (1 + (2 * sSN k a + 2 * sPbN k a)) *
        W ^ (P + (2 * swSW P k a D + 2 * swPbW P k a D)) := by
    have hPbv : clsPb (splitCnt V a D) M tS gamma S (rho / 4) =
        splitCnt V a D tS gamma (M * S) (rho / 4) := by
      unfold clsPb; rw [abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    have h := famPieceGraphBound_le_mul_sq (Pb := clsPb (splitCnt V a D) M tS gamma)
      (tb_one_le hν hW1) (tb_one_le hν hW1) hM hS
      (by rw [← hSdef, hPbv]; exact zero_le_one.trans hPb1)
      (by rw [← hSdef, hPbv]; exact hPb)
    convert h using 1; ring
  have h3k := (le_max_right _ _).trans hfac
  refine max_le (hG.trans (tb_mono hν hW1 (by unfold sCountN; omega) (by unfold swCountW; omega))) ?_
  refine h3k.trans (tb_mono hν hW1 (by unfold sCountN sPbN; nlinarith) ?_)
  unfold swCountW swPbW swSW swQrW
  nlinarith [Nat.le_mul_of_pos_left (swStepY P k a D) (Nat.two_pow_pos k)]

/-! ### The width exponent -/

def sErN (k a : Nat) : Nat := a * 2 ^ k
def sBqN (k a : Nat) : Nat := a * 2 ^ (k + 2)
def sLN (k a : Nat) : Nat := sBqN k a + (sErN k a + a)
/-- The family exponent of the width exponent of the next class. -/
def sExpN (k a : Nat) : Nat := 1 + sLN k a + sPbN k a

theorem pow_le_exp_mul {x : Real} (hx : 0 < x) (m : Nat) : x ^ m ≤ Real.exp (m * x) := by
  rw [← Real.exp_log (pow_pos hx m)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow]
  exact mul_le_mul_of_nonneg_left ((Real.log_le_sub_one_of_pos hx).trans (by linarith))
    (Nat.cast_nonneg _)

theorem nat_le_two_pow_real (m : Nat) {W : Real} (hW : 2 ≤ W) : (m : Real) ≤ W ^ m := by
  have h : (m : Real) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  exact h.trans (pow_le_pow_left₀ (by norm_num) hW m)

/-- Absorb the logarithmic width budget and its fixed cap factor in the parameter base. -/
theorem split_width_front_factor_le {ν W : Real} (hν : 1 ≤ ν) (hW : 2 ≤ W)
    (a b T : Nat) :
    2 * (6 + ((a : Real) * ν + ((b + 4 : Nat) : Real) * W + W ^ T)) ≤
      ν * W ^ (T + a + b + 11) := by
  have hW1 : 1 ≤ W := by linarith only [hW]
  set X := ν * W ^ (T + 1) with hXdef
  have hνX : ν ≤ X := le_mul_of_one_le_right (le_trans zero_le_one hν) (one_le_pow₀ hW1)
  have hWX : W ≤ X := (le_self_pow₀ hW1 (by omega : T + 1 ≠ 0)).trans
    (le_mul_of_one_le_left (by positivity) hν)
  have hTX : W ^ T ≤ X := (pow_le_pow_right₀ hW1 (by omega : T ≤ T + 1)).trans
    (le_mul_of_one_le_left (by positivity) hν)
  have hX1 : 1 ≤ X := hν.trans hνX
  have hsum : 2 * (6 + ((a : Real) * ν + ((b + 4 : Nat) : Real) * W + W ^ T)) ≤
      (2 * ((a + b : Nat) : Real) + 22) * X := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hνX (Nat.cast_nonneg a),
      mul_le_mul_of_nonneg_left hWX (by positivity : (0 : Real) ≤ (b : Real) + 4)]
  have hm := nat_le_two_pow_real (a + b) hW
  have hp : (1 : Real) ≤ W ^ (a + b) := one_le_pow₀ hW1
  have h24 : (24 : Real) ≤ W ^ 10 := (by norm_num : (24 : Real) ≤ 2 ^ 10).trans
    (pow_le_pow_left₀ (by norm_num) hW 10)
  have hc : 2 * ((a + b : Nat) : Real) + 22 ≤ W ^ (a + b + 10) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_right h24 (pow_nonneg (le_trans zero_le_one hW1) (a + b))]
  calc _ ≤ (2 * ((a + b : Nat) : Real) + 22) * X := hsum
    _ ≤ W ^ (a + b + 10) * X := mul_le_mul_of_nonneg_right hc (le_trans zero_le_one hX1)
    _ = ν * W ^ (T + a + b + 11) := by rw [hXdef]; simp only [pow_add]; ring

def sPbN2 (k ac ae : Nat) : Nat := ae * (sSN k ac + 1)
def sLN2 (k ac ae : Nat) : Nat := sBqN k ac + (sErN k ae + ae)
/-- The family exponent of the width exponent of the next two-track class. -/
def sExpN2 (k ac ae : Nat) : Nat := 1 + sLN2 k ac ae + sPbN2 k ac ae

/-- **The width exponent of the next class from a two-track class.** -/
theorem split_exp_inv_le_W2 {k ac Dc ae De P T m : Nat}
    {tS gS zeta : Real} (hac : 1 ≤ ac) (hDc : 1 ≤ Dc) (hae : 1 ≤ ae)
    (hDe : 1 ≤ De) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V')
    (hpV : (p : Real) ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat)
    (hm0 : (m : Real) ≤ (2 / (gamma * theta)) ^ P)
    (hgd0 : 2 / (gamma * tS) ≤ (2 / (gamma * theta)) ^ (P + 1))
    (hdd0 : 2 / (gS * tS) ≤ (2 / (gamma * theta)) ^ (P + 1))
    (hb : 0 < tS) (hb1 : tS ≤ 1) (hd : 0 < gS) (hd1 : gS ≤ 1)
    (hz : 0 < zeta ∧ zeta ≤ 1 ∧ zeta⁻¹ ≤ Real.exp ((2 / (gamma * theta)) ^ T)) (hPk : k + 8 ≤ P) :
    let M := n * m
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
            (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho *
          famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
            (clsEs (splitExp V ae De) M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (splitCnt V ac Dc tS gS M)
            (zeta) rho)
          (pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
            (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho)
          (famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
            (clsEs (splitExp V ae De) M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ ((n : Real) + 1) ^ sExpN2 k ac ae * splitW V' theta gamma rho ^ swExpW2 P T k ac Dc ae De := by
  intro M e
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, hdd⟩ := split_step_basics_W hV hVV hg hg1 ht ht1 hr hr1 n hm0 hgd0 hdd0
  obtain ⟨hfacE, -⟩ := split_Qr_le_W (k := k) hae hDe hV hVV hg hg1 ht ht1 hr hr1 n hm0 hgd0
    hdd0 hb hPk
  obtain ⟨hS, -, -, -⟩ := split_samples_le_W (k := k) hac hDc hV hVV hg hg1 ht ht1 hr hr1 n hm0
    hgd0 hdd0 hb hb1 hPk
  obtain ⟨hz0, hz1, hzi⟩ := hz
  have hu0 : 0 ≤ 2 / (gamma * theta) := (div_pos two_pos (mul_pos hg ht)).le
  have hnv := classVertexNum_succ_le k
  set ν : Real := (n : Real) + 1
  set W := splitW V' theta gamma rho
  clear_value W
  have hν : 1 ≤ ν := le_add_of_nonneg_left n.cast_nonneg
  have hW1 : 1 ≤ W := by linarith
  -- the counts at `ρ/8` of both tracks
  have hcb : ∀ a D : Nat, 1 ≤ splitCnt V a D tS gS M (rho / 8) ∧
      splitCnt V a D tS gS M (rho / 8) ≤ ν ^ a * W ^ swEbW P k a D := fun a D =>
    ⟨(splitCnt_controls hV a D).1 tS gS M _ hb hb1 hd hd1 (by positivity) (by linarith),
      (splitCnt_scaled_le (by linarith) hw2 hVw hν hb hd hr hrw (by norm_num)
        (by norm_num : (8 : Real) ≤ 2 ^ 3) hdd hM1).trans_eq (by unfold swEbW; ring)⟩
  obtain ⟨hcc1, hcc⟩ := hcb ac Dc
  obtain ⟨hce1, hce⟩ := hcb ae De
  -- the remainder exponent at `ρ/8`, from the exponent track
  have hcr0 : 0 < splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) := by
    unfold splitCnt splitW; positivity
  set cr := splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1))
  have hEr : clsEr (splitExp V ae De) k M tS gamma (rho / 8) =
      (cr⁻¹ / 16) ^ (classVertexNum k + 1) := Fin.prod_const _ _
  have hEri : (clsEr (splitExp V ae De) k M tS gamma (rho / 8))⁻¹ ≤
      ν ^ sErN k ae * W ^ swErW P k ae De := by
    rw [hEr, ← inv_pow, inv_div, div_inv_eq_mul]
    have h16 := tb_const_mul hw2 (by norm_num : (16 : Real) ≤ 2 ^ 4) hcr0.le
      ((le_max_left _ _).trans hfacE)
    refine ((pow_le_pow_left₀ (by linarith) h16 _).trans
      (pow_le_pow_right₀ (tb_one_le hν hW1) hnv)).trans_eq ?_
    unfold sErN swErW; ring
  -- the divisor and the prefactor, from the count track
  set q := ⌊splitCnt V ac Dc tS gS M (rho / 8)⌋₊
  have hq1 : ((q + 1 : Nat) : Real) ≤ ν ^ ac * W ^ (swEbW P k ac Dc + 1) := by
    push_cast; exact tb_add_one hν hw2 ((Nat.floor_le (by linarith)).trans hcc)
  have hpW : (p : Real) ≤ W := hpV.trans hV'w
  have hKW : (K : Real) ≤ W := hKV.trans hV'w
  have hBq : familyWidthDivisor k p q ≤ ν ^ sBqN k ac * W ^ swBqW P k ac Dc := by
    calc familyWidthDivisor k p q = 8 * p * ((q + 1 : Nat) : Real) ^ 2 ^ (k + 2) := by
          unfold familyWidthDivisor; push_cast; ring
      _ ≤ W ^ 3 * W * (ν ^ ac * W ^ (swEbW P k ac Dc + 1)) ^ 2 ^ (k + 2) := by
          gcongr; exact const_le_pow hw2 (by norm_num)
      _ = ν ^ sBqN k ac * W ^ swBqW P k ac Dc := by unfold sBqN swBqW; ring
  have hA1 : 1 ≤ familyWidthPrefactor K q := (by norm_num : (1 : Real) ≤ 4).trans
    (le_mul_of_one_le_right (by norm_num) (Nat.one_le_cast.mpr (Nat.mul_pos hK q.succ_pos)))
  have hA : familyWidthPrefactor K q ≤ ν ^ ac * W ^ (swEbW P k ac Dc + 4) := by
    calc familyWidthPrefactor K q = 4 * K * ((q + 1 : Nat) : Real) := by
          unfold familyWidthPrefactor; push_cast; ring
      _ ≤ W ^ 2 * W * (ν ^ ac * W ^ (swEbW P k ac Dc + 1)) := by
          gcongr; exact const_le_pow hw2 (by norm_num)
      _ = ν ^ ac * W ^ (swEbW P k ac Dc + 4) := by ring
  -- the line exponent
  set L := pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
    (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho with hLdef
  have hEr0 : 0 < clsEr (splitExp V ae De) k M tS gamma (rho / 8) := by
    rw [hEr]; exact pow_pos (div_pos (inv_pos.mpr hcr0) (by norm_num)) _
  have hEb0 : 0 < splitExp V ae De tS gS M (rho / 8) := inv_pos.mpr (zero_lt_one.trans_le hce1)
  have hL0 : 0 < L := div_pos (mul_pos hEr0 hEb0) (familyWidthDivisor_pos hp q)
  have hLi : L⁻¹ ≤ ν ^ sLN2 k ac ae * W ^ swLW2 P k ac Dc ae De := by
    rw [hLdef, pieceLineExponent, inv_div, div_eq_mul_inv, mul_inv]
    exact tb_mul hν hW1 (by positivity) hBq
      (tb_mul hν hW1 (by positivity) hEri ((inv_inv _).trans_le hce))
  -- the slice exponent: samples from the count track, slices from the exponent track
  set S := famPieceSamples (clsQr (splitCnt V ac Dc) k M tS gamma) M rho
  have hMS : ((M * S : Nat) : Real) + 1 ≤ ν ^ (1 + sSN k ac) * W ^ (P + swSW P k ac Dc + 1) := by
    push_cast; exact tb_add_one hν hw2 (tb_mul hν hW1 (Nat.cast_nonneg _) hM hS)
  have hPb1 := (splitCnt_controls hV ae De).1 tS gamma (M * S) (rho / 4) hb hb1 hg hg1
    (by positivity) (by linarith)
  set Sl := famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
    (clsEs (splitExp V ae De) M tS gamma) M rho
  have hSlval : Sl = (splitCnt V ae De tS gamma (M * S) (rho / 4))⁻¹ := by
    rw [← abs_of_pos (by positivity : (0 : Real) < rho / 4)]; rfl
  obtain ⟨hSl0, hSl1, hSli⟩ : 0 < Sl ∧ Sl ≤ 1 ∧
      Sl⁻¹ ≤ ν ^ sPbN2 k ac ae * W ^ swPbW2 P k ac Dc ae De := by
    rw [hSlval, inv_inv]
    exact ⟨inv_pos.mpr (zero_lt_one.trans_le hPb1), inv_le_one_of_one_le₀ hPb1,
      (splitCnt_scaled_le (by linarith) hw2 hVw hν hb hg hr hrw four_pos
        (by norm_num : (4 : Real) ≤ 2 ^ 2) hgd hMS).trans_eq (by unfold sPbN2 swPbW2; ring)⟩
  -- the width scale `ζ/A`, from the count track
  have hA0 : 0 < familyWidthPrefactor K q := zero_lt_one.trans_le hA1
  set Λ := (ac : Real) * ν + ((swEbW P k ac Dc + 4 : Nat) : Real) * W + W ^ T with hΛdef
  have hzinv : (zeta / familyWidthPrefactor K q)⁻¹ ≤ Real.exp Λ := by
    rw [inv_div, div_eq_mul_inv, hΛdef, Real.exp_add, Real.exp_add]
    refine mul_le_mul (hA.trans (mul_le_mul (pow_le_exp_mul (by linarith) ac)
      (pow_le_exp_mul (by linarith) _) (by positivity) (by positivity)))
      (hzi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hu0 huw _))) (by positivity)
      (by positivity)
  -- the cap
  set R := ν ^ (sLN2 k ac ae + sPbN2 k ac ae) *
    W ^ (2 + (swLW2 P k ac Dc ae De + swPbW2 P k ac Dc ae De)) with hRdef
  have hR1 : 1 ≤ R := tb_one_le hν hW1
  have hLSR : (L * Sl / 4)⁻¹ ≤ R := by
    rw [show (L * Sl / 4)⁻¹ = 4 * (L⁻¹ * Sl⁻¹) by ring]
    exact tb_const_mul hw2 (by norm_num) (by positivity) (tb_mul hν hW1 (by positivity) hLi hSli)
  have hcap := capped_rounded_inv_le_real hL0 hSl0 hSl1 (div_pos hz0 hA0)
    ((div_le_one hA0).mpr (hz1.trans hA1)) (by positivity) hzinv hR1
    (hLi.trans (tb_mono hν hW1 (by omega) (by omega))) hLSR
  refine ⟨section16CappedWidthExponent_pos (div_pos (mul_pos hL0 hSl0) (by norm_num)),
    hcap.trans ?_⟩
  have hfront : 2 * (6 + Λ) ≤ ν * W ^ (swZW P T k ac Dc + 4) := by
    simpa only [hΛdef, swZW, Nat.add_assoc] using
      split_width_front_factor_le hν hw2 ac (swEbW P k ac Dc) (T)
  rw [← mul_assoc]
  refine (mul_le_mul_of_nonneg_right hfront (by positivity)).trans_eq ?_
  rw [hRdef]; unfold sExpN2 swExpW2; ring

/-! ### The split step -/

/-- The family exponent of the next split class. -/
def splitStepA (k a : Nat) : Nat := sCountN k a + sExpN k a

end LeanProofs.GowersSzemeredi
