import GowersSzemeredi.Proofs18LengthSixParameters
import GowersSzemeredi.Proofs18ExponentialCalculus

/-! The local threshold of the length-six route is single exponential.

The modulus threshold `lsTloc` of `ls_modulus_conditions` is a maximum of
two kinds of term: Lemma 15.6's threshold, and powers `c^(1/a)` whose
exponents `a` are the polynomially small width exponents of
`Proofs18LengthSixParameters`. With `X = 2/α` and recurrence constants
`K₁, p₁, K₂, p₂ ≤ X³`:
* `sixWThr ≤ exp(X^(N+7))` at a density `t` whose width exponents are
  `≥ X^(-N)`;
* `lsMThr ≤ exp(X^(2^456))`, and `lsMReq ≤ exp(X^(2^510))`;
* `lemma156ExplicitThreshold 2 (α/2) (α/2) ≤ X^(2^81)`;
* `lsTloc_le_exp : lsTloc ≤ exp(X^(2^644))`.

The calculus: `b ≤ exp(X^m)` and `e ≤ X^k` give `b^e ≤ exp(X^(m+k))`. Sums
and products of two terms below `exp(X^m)` are below `exp(X^(m+1))`. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The exponential calculus -/

/-! ### The lift thresholds -/

/-- The lift threshold `sixWThr` from the inverse width exponents. -/
theorem sixWThr_le_exp {Eb : Nat → Real → Real → Real → Real} {alpha t X : Real} {N : Nat}
    (hX : 2 ≤ X)
    (h1 : 0 < Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2))
    (h1i : (Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2))⁻¹ ≤ X ^ N)
    (h2 : 0 < Eb 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2))
    (h2i : (Eb 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2))⁻¹ ≤ X ^ N) :
    sixWThr Eb alpha t ≤ Real.exp (X ^ (N + 7)) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  unfold sixWThr
  dsimp only
  set E1 := Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2)
  set E2 := Eb 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (t / 2 / 2)
  clear_value E1 E2
  have h6 : (6 : Real) ≤ Real.exp (X ^ 3) := const_le_exp_pow hX (by norm_num)
  have h4E : ∀ E : Real, 0 < E → E⁻¹ ≤ X ^ N → (6 : Real) ^ (4 / E) ≤ Real.exp (X ^ (3 + (2 + N))) := by
    intro E hE hEi
    apply rpow_le_exp_pow hX (by norm_num) h6 (by positivity)
    rw [div_eq_mul_inv, pow_add]
    exact mul_le_mul (const_le_pow hX (by norm_num)) hEi (inv_pos.mpr hE).le (pow_nonneg hX0 _)
  have hA := h4E E1 h1 h1i
  have hB : (6 : Real) ^ (4 / (E1 / 4)) ≤ Real.exp (X ^ (3 + (4 + N))) := by
    apply rpow_le_exp_pow hX (by norm_num) h6 (by positivity)
    rw [show 4 / (E1 / 4) = 16 * E1⁻¹ by field_simp; ring, pow_add]
    exact mul_le_mul (const_le_pow hX (by norm_num)) h1i (inv_pos.mpr h1).le (pow_nonneg hX0 _)
  have hC := h4E E2 h2 h2i
  have h8 : (8 * 0 + 8 : Real) ≤ Real.exp (X ^ (N + 5)) := (const_le_exp_pow (j := 3) hX (by norm_num)).trans
    (exp_pow_mono hX (by omega))
  have hmax1 : max (8 * 0 + 8) ((6 : Real) ^ (4 / E1)) ≤ Real.exp (X ^ (N + 5)) :=
    max_le h8 (hA.trans (exp_pow_mono hX (by omega)))
  have hmul : 8 * max (8 * 0 + 8) ((6 : Real) ^ (4 / E1)) ≤ Real.exp (X ^ (N + 5 + 1)) :=
    exp_mul_le hX (le_trans (by norm_num) (le_max_left _ _))
      ((const_le_exp_pow (j := 3) hX (by norm_num)).trans (exp_pow_mono hX (by omega))) hmax1
  have hsum : 8 * max (8 * 0 + 8) ((6 : Real) ^ (4 / E1)) + 8 ≤ Real.exp (X ^ (N + 5 + 1 + 1)) :=
    exp_add_le hX hmul ((const_le_exp_pow (j := 3) hX (by norm_num)).trans (exp_pow_mono hX (by omega)))
  apply max_le (max_le (hsum.trans (exp_pow_mono hX (by omega)))
    (hB.trans (exp_pow_mono hX (by omega))))
  exact max_le (h8.trans (exp_pow_mono hX (by omega))) (hC.trans (exp_pow_mono hX (by omega)))

/-- `sixWThr` at a density `t` with `t⁻¹ ≤ X^e`, for the length-six controls. -/
theorem sixWThr_ls_le_exp {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {alpha t : Real} {e : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (ht : 0 < t) (ht1 : t ≤ 1) (hte : t⁻¹ ≤ (2 / alpha) ^ e)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3) :
    sixWThr (sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)) alpha t ≤
      Real.exp ((2 / alpha) ^ ((1 + 1 + (2 : Nat) ^ 133 + (e + 3)) * (2 : Nat) ^ 132 + 7)) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  have hinv8 : (t / 2 / 2 / 2)⁻¹ ≤ (2 / alpha) ^ (e + 3) := by
    rw [show (t / 2 / 2 / 2)⁻¹ = 8 * t⁻¹ by field_simp; ring, pow_add, mul_comm]
    exact mul_le_mul hte (const_le_pow hX2 (by norm_num)) (by norm_num) (pow_nonneg hX0 _)
  have hinv4 : (t / 2 / 2)⁻¹ ≤ (2 / alpha) ^ (e + 3) := by
    rw [show (t / 2 / 2)⁻¹ = 4 * t⁻¹ by field_simp; ring, pow_add, mul_comm]
    exact mul_le_mul hte (const_le_pow hX2 (by norm_num)) (by norm_num) (pow_nonneg hX0 _)
  obtain ⟨h10, h1i⟩ := sixEb_half_budget_inv_le 1 hK1 hp1 ha ha2 (by positivity)
    (by linarith only [ht1]) hinv8 hK hp
  obtain ⟨h20, h2i⟩ := sixEb_half_budget_inv_le 2 hK1 hp1 ha ha2 (by positivity)
    (by linarith only [ht1]) hinv4 hK hp
  exact sixWThr_le_exp hX2 h10 h1i h20 h2i

/-- The nested lift threshold and the spectrum-scale threshold `lsMThr`. -/
theorem lsMThr_le_exp {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3) :
    lsMThr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) alpha ≤
      Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 456)) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  obtain ⟨⟨t0, t1, ti⟩, ⟨u0, u1, ui⟩, ⟨v0, v1, vi⟩⟩ := lsC_T2_bounds ha ha2
  have hWt := sixWThr_ls_le_exp hK1 hp1 ha ha2 t0 t1 ti hK hp
  have hWu := sixWThr_ls_le_exp hK1 hp1 ha ha2 u0 u1 ui hK hp
  have hWv := sixWThr_ls_le_exp hK1 hp1 ha ha2 v0 v1 vi hK hp
  obtain ⟨a0, ai⟩ := sixWExp_inv_le hK1 hp1 ha ha2 t0 t1 ti hK hp
  obtain ⟨b0, bi⟩ := sixWExp_inv_le hK1 hp1 ha ha2 u0 u1 ui hK hp
  obtain ⟨n0, -, ni⟩ := lsNestExp_bounds hK1 hp1 ha ha2 hK hp
  set Eb := sixEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)
  set X := 2 / alpha with hX
  clear_value X
  have hW1 : ∀ s, 1 ≤ sixWThr Eb alpha s := fun s => one_le_sixWThr Eb alpha s
  unfold lsMThr lsNestThr
  apply max_le (max_le (max_le (hWt.trans (exp_pow_mono hX2 (by norm_num))) ?_) ?_) ?_
  · -- `W(C t)^(1/a_t)`
    rw [one_div]
    exact (rpow_le_exp_pow hX2 (hW1 _) hWu (inv_pos.mpr a0).le ai).trans
      (exp_pow_mono hX2 (by norm_num))
  · -- `W(C(C t))^(1/(a_t a_{C t}))`
    rw [one_div, mul_inv]
    exact (rpow_le_exp_pow hX2 (hW1 _) hWv (by positivity)
      (mul_le_pow_add (inv_pos.mpr a0).le (inv_pos.mpr b0).le ai bi (by linarith only [hX2]))).trans
      (exp_pow_mono hX2 (by norm_num))
  · rw [one_div]
    exact (rpow_le_exp_pow (m := 6) hX2 (by norm_num) (const_le_exp_pow hX2 (by norm_num))
      (inv_pos.mpr n0).le ni).trans (exp_pow_mono hX2 (by norm_num))


/-! ### The modulus requirement -/

theorem multipleS_two_half_eq (alpha : Real) (ha : 0 < alpha) :
    multipleS alpha (alpha / 2) 2 = (2 / alpha) ^ ((2 : Nat) ^ 257) := by
  unfold multipleS
  rw [show 2 / (alpha * (alpha / 2)) = (2 / alpha) ^ 2 by field_simp, ← pow_mul]
  norm_num

theorem lsZeta_bounds {alpha : Real} (ha : 0 < alpha) :
    0 < lsZeta alpha ∧ lsZeta alpha ≤ 1 ∧
      (lsZeta alpha)⁻¹ ≤ Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 257)) := by
  have hm0 : 0 ≤ multipleS alpha (alpha / 2) 2 := by
    rw [multipleS_two_half_eq alpha ha]; positivity
  unfold lsZeta section16Zeta
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hm0])
  · rw [Real.rpow_neg (by norm_num), inv_inv, Real.rpow_def_of_pos (by norm_num),
      ← multipleS_two_half_eq alpha ha]
    apply Real.exp_le_exp.mpr
    have h : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
    calc Real.log 2 * multipleS alpha (alpha / 2) 2 ≤ 1 * multipleS alpha (alpha / 2) 2 :=
          mul_le_mul_of_nonneg_right h hm0
      _ = multipleS alpha (alpha / 2) 2 := one_mul _

theorem lsMReq_le_exp {K2 p2 : Nat} (hK2 : 0 < K2) (hp2 : 0 < p2) {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K2 : Real) ≤ (2 / alpha) ^ 3) (hp : (p2 : Real) ≤ (2 / alpha) ^ 3) :
    1 ≤ lsMReq K2 p2 alpha ∧ lsMReq K2 p2 alpha ≤ Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 510)) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  have hq := lsQM_le_power ha ha2
  obtain ⟨b0, -, bi⟩ := lsB_bounds hp2 ha ha2 hp
  obtain ⟨z0, z1, zi⟩ := lsZeta_bounds ha
  obtain ⟨r0, r1, ri⟩ := lsRho_bounds ha ha2
  have hthr1 : (1 : Real) ≤ (familyRecThr 2 K2 p2 (lsQM alpha) : Real) :=
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr
      (familyRecThr_pos (k := 2) (p := p2) (show 1 ≤ K2 by omega) (lsQM alpha)).ne')
  refine ⟨hthr1.trans (le_max_left _ _), ?_⟩
  unfold lsMReq
  set q := lsQM alpha
  set B := lsB p2 alpha
  set z := lsZeta alpha
  set r := lsRho alpha
  set X := 2 / alpha with hX
  clear_value q B z r X
  -- the recurrence threshold `(K₂ (q+1))^(2 p₂ (q+1)^16)`
  have hq1 : ((q + 1 : Nat) : Real) ≤ X ^ ((2 : Nat) ^ 504 + 1) := by
    rw [Nat.cast_succ]; exact add_le_pow_succ hX2 hq (one_le_pow_of_two_le hX2 _)
  have hbase : ((K2 * (q + 1) : Nat) : Real) ≤ X ^ (3 + ((2 : Nat) ^ 504 + 1)) := by
    rw [Nat.cast_mul]; exact mul_le_pow_add (Nat.cast_nonneg _) (Nat.cast_nonneg _) hK hq1 hX0
  have hexpo : ((2 * (p2 * (q + 1) ^ (2 * 2 ^ (2 + 1))) : Nat) : Real) ≤
      X ^ (1 + (3 + ((2 : Nat) ^ 504 + 1) * 16)) := by
    have h16 : ((q + 1 : Nat) : Real) ^ 16 ≤ X ^ (((2 : Nat) ^ 504 + 1) * 16) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hq1 16
    have : ((2 * (p2 * (q + 1) ^ (2 * 2 ^ (2 + 1))) : Nat) : Real) =
        2 * ((p2 : Real) * ((q + 1 : Nat) : Real) ^ 16) := by push_cast; ring
    rw [this, pow_add, pow_one]
    exact mul_le_mul hX2 (mul_le_pow_add (Nat.cast_nonneg _) (by positivity) hp h16 hX0)
      (by positivity) hX0
  have hb1 : (1 : Real) ≤ ((K2 * (q + 1) : Nat) : Real) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hT : (familyRecThr 2 K2 p2 q : Real) ≤
      Real.exp (X ^ (3 + ((2 : Nat) ^ 504 + 1) + (1 + (3 + ((2 : Nat) ^ 504 + 1) * 16)))) := by
    unfold familyRecThr
    rw [Nat.cast_pow]
    exact natpow_le_exp_pow hX2 hb1 (le_exp_pow_of_le_pow hbase) hexpo
  -- the three Bohr-radius terms
  have hzX : z⁻¹ ≤ Real.exp (X ^ ((2 : Nat) ^ 416)) := zi.trans (exp_pow_mono hX2 (by norm_num))
  have h8z : 8 / z ≤ Real.exp (X ^ ((2 : Nat) ^ 416 + 1)) := by
    rw [div_eq_mul_inv]
    exact exp_mul_le hX2 (inv_pos.mpr z0).le
      ((const_le_exp_pow (j := 3) hX2 (by norm_num)).trans (exp_pow_mono hX2 (by norm_num))) hzX
  have h16z : 16 / z ≤ Real.exp (X ^ ((2 : Nat) ^ 416 + 1)) := by
    rw [div_eq_mul_inv]
    exact exp_mul_le hX2 (inv_pos.mpr z0).le
      ((const_le_exp_pow (j := 4) hX2 (by norm_num)).trans (exp_pow_mono hX2 (by norm_num))) hzX
  have hr3 : (r ^ 3)⁻¹ ≤ Real.exp (X ^ ((2 : Nat) ^ 416 + 1)) := by
    rw [← inv_pow]
    refine le_exp_pow_of_le_pow ((pow_le_pow_left₀ (inv_pos.mpr r0).le ri 3).trans ?_)
    rw [← pow_mul]; exact pow_le_pow_right₀ hX1 (by norm_num)
  have h4zr : 4 / (z * r ^ 3) ≤ Real.exp (X ^ ((2 : Nat) ^ 416 + 1 + 1)) := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc]
    exact exp_mul_le hX2 (inv_pos.mpr (pow_pos r0 3)).le
      (exp_mul_le hX2 (inv_pos.mpr z0).le
        ((const_le_exp_pow (j := 2) hX2 (by norm_num)).trans (exp_pow_mono hX2 (by norm_num)))
        hzX |>.trans (exp_pow_mono hX2 le_rfl)) hr3
  have hz1' : 1 ≤ z⁻¹ := (one_le_inv₀ z0).mpr z1
  have hBi0 : 0 ≤ 1 / B := by positivity
  have hBe : 1 / B ≤ X ^ ((2 : Nat) ^ 509) := by rw [one_div]; exact bi
  have hBe2 : 2 / B ≤ X ^ (1 + (2 : Nat) ^ 509) := by
    rw [div_eq_mul_inv, pow_add, pow_one]; exact mul_le_mul hX2 bi (inv_pos.mpr b0).le hX0
  have h8z1 : 1 ≤ 8 / z := by rw [le_div_iff₀ z0]; linarith only [z1]
  have h16z1 : 1 ≤ 16 / z := by rw [le_div_iff₀ z0]; linarith only [z1]
  have h4zr1 : 1 ≤ 4 / (z * r ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    have : r ^ 3 ≤ 1 := pow_le_one₀ r0.le r1
    nlinarith only [this, z1, z0, pow_pos r0 3]
  apply max_le (hT.trans (exp_pow_mono hX2 (by norm_num)))
  apply max_le ((rpow_le_exp_pow hX2 h8z1 h8z hBi0 hBe).trans (exp_pow_mono hX2 (by norm_num)))
  apply max_le ((rpow_le_exp_pow hX2 h4zr1 h4zr hBi0 hBe).trans (exp_pow_mono hX2 (by norm_num)))
  exact (rpow_le_exp_pow hX2 h16z1 h16z (by positivity) hBe2).trans (exp_pow_mono hX2 (by norm_num))

/-! ### Lemma 15.6's threshold in dimension two -/

theorem lemma156ExplicitThreshold_two_half_le {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    lemma156ExplicitThreshold 2 (alpha / 2) (alpha / 2) ≤ (2 / alpha) ^ ((2 : Nat) ^ 81) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hXa : (alpha / 2)⁻¹ = 2 / alpha := inv_div _ _
  set u := 2 / alpha with hu
  clear_value u
  have hinv : u⁻¹ = alpha / 2 := by rw [← hXa, inv_inv]
  have hbase : (u ^ 3136)⁻¹ ≤ (alpha / 2) ^ (7 * 4 ^ (2 + 1)) * (alpha / 2) ^ (21 * 2 * 4 ^ (2 + 1)) := by
    rw [← pow_add, ← hinv, inv_pow]
    norm_num
  exact lemma156ExplicitThreshold_le_power_of_selection_base (by norm_num) hX2 hbase
    (by norm_num [arrangementSelectionExponent])

/-! ### The local threshold -/

/-- **The modulus threshold of the length-six route is single exponential**:
`lsTloc ≤ exp((2/α)^(2^644))`. -/
theorem lsTloc_le_exp {K1 p1 K2 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) (hK2 : 0 < K2)
    (hp2 : 0 < p2) {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3)
    (hK' : (K2 : Real) ≤ (2 / alpha) ^ 3) (hp' : (p2 : Real) ≤ (2 / alpha) ^ 3) :
    lsTloc (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) K2 p2 alpha ≤
      Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 644)) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  have hL := lemma156ExplicitThreshold_two_half_le ha ha2
  have hM := lsMThr_le_exp hK1 hp1 ha ha2 hK hp
  obtain ⟨n0, -, ni⟩ := lsNestExp_bounds hK1 hp1 ha ha2 hK hp
  obtain ⟨q1, hq⟩ := lsMReq_le_exp hK2 hp2 ha ha2 hK' hp'
  obtain ⟨m0, mi⟩ := lsMExp_bounds hK1 hp1 ha ha2 hK hp
  obtain ⟨e0, ei⟩ := lsE_inv_le_power hK1 hp1 hp2 ha ha2 hK hp hp'
  obtain ⟨f0, fi⟩ := lsF_bounds hK1 hp1 hp2 ha ha2 hK hp hp'
  set X := 2 / alpha with hX
  clear_value X
  have hf2 : 2 / lsF (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha ≤
      X ^ (1 + (2 : Nat) ^ 642) := by
    rw [div_eq_mul_inv, pow_add, pow_one]; exact mul_le_mul hX2 fi (inv_pos.mpr f0).le hX0
  unfold lsTloc
  apply max_le
  · exact max_le ((const_le_exp_pow (j := 2) hX2 (by norm_num)).trans
      (exp_pow_mono hX2 (by norm_num)))
      ((le_exp_pow_of_le_pow hL).trans (exp_pow_mono hX2 (by norm_num)))
  apply max_le (hM.trans (exp_pow_mono hX2 (by norm_num)))
  apply max_le
  · rw [one_div]
    exact (rpow_le_exp_pow hX2 (by norm_num) (const_le_exp_pow (j := 2) hX2 (by norm_num))
      (inv_pos.mpr n0).le ni).trans (exp_pow_mono hX2 (by norm_num))
  apply max_le
  · rw [one_div]
    exact (rpow_le_exp_pow hX2 q1 hq (inv_pos.mpr m0).le mi).trans (exp_pow_mono hX2 (by norm_num))
  apply max_le
  · rw [one_div]
    exact (rpow_le_exp_pow hX2 (by norm_num) (const_le_exp_pow (j := 3) hX2 (by norm_num))
      (inv_pos.mpr e0).le ei).trans (exp_pow_mono hX2 (by norm_num))
  · exact (rpow_le_exp_pow hX2 (by norm_num) (const_le_exp_pow (j := 3) hX2 (by norm_num))
      (by positivity) hf2).trans (exp_pow_mono hX2 (by norm_num))
end LeanProofs.GowersSzemeredi
