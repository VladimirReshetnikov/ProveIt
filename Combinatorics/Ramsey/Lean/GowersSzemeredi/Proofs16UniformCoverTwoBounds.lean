import GowersSzemeredi.Proofs16UniformCoverTwo
import GowersSzemeredi.Proofs18LengthSixExponents

/-! Envelope controls for the uniform cover in dimension two (Notes L.5, D1).

The controls of `section16_uniform_cover_two` at `M` pieces are polynomial in
any base `w` with `2/(γθ) ≤ w`, `ρ⁻¹ ≤ w` and `M ≤ w^(2^84)`:
* `uniTwoCount_le_power : uniTwoCount θ γ M ρ ≤ w^(2^89)`;
* `uniTwoExp_inv_le_power : (uniTwoExp A Bq θ γ M ρ)⁻¹ ≤ w^(2^130)`, for
  `A = familyWidthPrefactor K₁` and `Bq = familyWidthDivisor 1 p₁` with
  `K₁, p₁ ≤ w³`;
* `uniTwoExp_pos`.

These are `polyTwoFamCount_le_power` and `polyTwoFamExp_inv_le_power` with the
piece count `polyTwoPieces γ θ` replaced by an arbitrary `M`, and the base
`2/(γθρ)` by an arbitrary `w`. A free base lets the family size and the
recurrence constants be absorbed into `w`, which gives envelopes monotone in
the family size. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

theorem uniTwoExp_pos {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q)
    {theta gamma : Real} (M : Nat) {rho : Real} (hrho : 0 < rho) :
    0 < uniTwoExp A Bq theta gamma M rho := by
  unfold uniTwoExp
  apply section16CappedWidthExponent_pos
  have h8 : 0 < rho / 8 := by positivity
  have h4 : 0 < rho / 4 := by positivity
  have hEb := cubicBaseExponent_pos
    (Nat.succ_pos (M * polyPieceSpecCount theta gamma)) h8
  have hEr := cubicBaseExponent_pos
    (Nat.succ_pos (M * polyPieceFaceCount theta gamma)) h8
  have hEs := cubicBaseExponent_pos (Nat.succ_pos (M *
    (famPieceSamples (famTwoQr (M) (polyPieceFaceCount theta gamma))
      (M) rho * polyPieceFaceCount theta gamma))) h4
  have hBq := hB ⌊famTwoQb (M) (polyPieceSpecCount theta gamma)
    (rho / 8)⌋₊
  simp only [pieceLineExponent, famPieceSliceExponent, famTwoEb, famTwoEr, famTwoEs]
  positivity

theorem uniTwoCount_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1)
    {w : Real} (hvw : 2 / (gamma * theta) ≤ w) (hrw : rho⁻¹ ≤ w)
    {M : Nat} (hM : (M : Real) ≤ w ^ ((2 : Nat) ^ 84)) :
    uniTwoCount theta gamma M rho ≤ w ^ ((2 : Nat) ^ 89) := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := polyPieceFaceCount_le_power hg hg1 ht ht1
  set v := 2 / (gamma * theta) with hv
  clear_value v
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  -- both counts below `w^(2^84)`
  have hm' : (M : Real) ≤ w ^ ((2 : Nat) ^ 84) := hM
  have hq' : (polyPieceFaceCount theta gamma : Real) ≤ w ^ ((2 : Nat) ^ 84) :=
    hq.trans (pow_le_pow_left₀ hv0 hvw _)
  set m := M with hmM
  set ql := polyPieceFaceCount theta gamma
  have hQr := famTwoQr_le_power hw2 hm' hq' (rho / 8)
  have hS := famPieceSamples_le_power (Qr := famTwoQr m ql) hw2 hr hrw hQr hm'
  have hP := famTwoPb_le_power hw2 hm' hq' hS (rho / 4)
  have hP0 : 0 ≤ famTwoPb m ql (famPieceSamples (famTwoQr m ql) m rho) (rho / 4) := by
    unfold famTwoPb; exact Nat.cast_nonneg _
  have hG := famPieceGraphBound_le_power (Pb := famTwoPb m ql) hw2 hm' hS hP0 hP
  unfold uniTwoCount
  apply max_le
  · exact le_pow_mono hw2 (by norm_num) hG
  · have h9 : ((3 ^ (1 + 1) * m : Nat) : Real) ≤ w ^ (4 + (2 : Nat) ^ 84) := by
      rw [Nat.cast_mul]
      exact const_mul_le_pow hw2 (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) hm'
    exact le_pow_mono hw2 (by norm_num) h9

theorem uniTwoExp_inv_le_power {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    {w : Real} (hvw : 2 / (gamma * theta) ≤ w) (hrw : rho⁻¹ ≤ w)
    {M : Nat} (hM : (M : Real) ≤ w ^ ((2 : Nat) ^ 84))
    (hK : (K1 : Real) ≤ w ^ 3)
    (hp : (p1 : Real) ≤ w ^ 3) :
    (uniTwoExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) theta gamma M rho)⁻¹ ≤
      w ^ ((2 : Nat) ^ 130) := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hζ0, hζ1, hζi⟩ := section16Zeta_one_bounds hg ht
  have hqs := polyPieceSpecCount_le_power hg hg1 ht ht1
  have hqf := polyPieceFaceCount_le_power hg hg1 ht ht1
  unfold uniTwoExp
  dsimp only
  set ζ := section16Zeta theta gamma 1
  set m := M with hmM
  set qs := polyPieceSpecCount theta gamma
  set qf := polyPieceFaceCount theta gamma
  set v := 2 / (gamma * theta) with hv
  clear_value v ζ m qs qf
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw2
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hm' : (m : Real) ≤ w ^ ((2 : Nat) ^ 84) := hM
  have hqs' : (qs : Real) ≤ w ^ ((2 : Nat) ^ 84) := hqs.trans (pow_le_pow_left₀ hv0 hvw _)
  have hqf' : (qf : Real) ≤ w ^ ((2 : Nat) ^ 84) := hqf.trans (pow_le_pow_left₀ hv0 hvw _)
  have hζw : ζ⁻¹ ≤ Real.exp (w ^ ((2 : Nat) ^ 128)) :=
    hζi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hv0 hvw _))
  have hr8 : (rho / 8)⁻¹ ≤ w ^ 4 := by
    rw [inv_div, div_eq_mul_inv, pow_succ]
    exact mul_le_mul (const_le_pow hw2 (by norm_num)) hrw
      (inv_pos.mpr hr).le (pow_nonneg hw0 _)
  have hr4 : (rho / 4)⁻¹ ≤ w ^ 3 := by
    rw [inv_div, div_eq_mul_inv, pow_succ]
    exact mul_le_mul (const_le_pow hw2 (by norm_num)) hrw
      (inv_pos.mpr hr).le (pow_nonneg hw0 _)
  -- the counts `m qs + 1`, `m qf + 1` and `n = 3 (m qs + 1)`
  have hmqs : ((m * qs + 1 : Nat) : Real) ≤ w ^ ((2 : Nat) ^ 84 + (2 : Nat) ^ 84 + 1) := by
    have h := nat_mul_le_pow hw2 hm' hqs'
    push_cast; push_cast at h
    exact add_le_pow_succ hw2 h (one_le_pow_of_two_le hw2 _)
  have hmqf : ((m * qf + 1 : Nat) : Real) ≤ w ^ ((2 : Nat) ^ 84 + (2 : Nat) ^ 84 + 1) := by
    have h := nat_mul_le_pow hw2 hm' hqf'
    push_cast; push_cast at h
    exact add_le_pow_succ hw2 h (one_le_pow_of_two_le hw2 _)
  have hn' : ((3 * (m * qs + 1) : Nat) : Real) ≤
      w ^ (2 + ((2 : Nat) ^ 84 + (2 : Nat) ^ 84 + 1)) := by
    rw [Nat.cast_mul]
    exact const_mul_le_pow hw2 (by norm_num) (by norm_num) (Nat.cast_nonneg _) hmqs
  have hn1 : ((3 * (m * qs + 1) + 1 : Nat) : Real) ≤
      w ^ (2 + ((2 : Nat) ^ 84 + (2 : Nat) ^ 84 + 1) + 1) := by
    rw [Nat.cast_succ]
    exact add_le_pow_succ hw2 hn' (one_le_pow_of_two_le hw2 _)
  have hfloor : ⌊famTwoQb m qs (rho / 8)⌋₊ = 3 * (m * qs + 1) := by
    unfold famTwoQb; exact Nat.floor_natCast _
  -- the line exponent
  have hBq : familyWidthDivisor 1 p1 (3 * (m * qs + 1)) ≤
      w ^ (3 + (3 + (2 + ((2 : Nat) ^ 84 + (2 : Nat) ^ 84 + 1) + 1) * 8)) := by
    have hval : familyWidthDivisor 1 p1 (3 * (m * qs + 1)) =
        8 * ((p1 : Real) * ((3 * (m * qs + 1) + 1 : Nat) : Real) ^ 8) := by
      unfold familyWidthDivisor; push_cast; ring
    rw [hval, pow_add, pow_add, pow_mul]
    exact mul_le_mul (const_le_pow hw2 (by norm_num))
      (mul_le_mul hp (pow_le_pow_left₀ (Nat.cast_nonneg _) hn1 8) (by positivity)
        (pow_nonneg hw0 _)) (by positivity) (pow_nonneg hw0 _)
  have hBq0 : 0 < familyWidthDivisor 1 p1 (3 * (m * qs + 1)) := familyWidthDivisor_pos hp1 _
  have hEb0 : 0 < famTwoEb m qs (rho / 8) :=
    cubicBaseExponent_pos (Nat.succ_pos _) (by positivity)
  have hEb : (famTwoEb m qs (rho / 8))⁻¹ ≤
      w ^ (27 + 4 * 3 + ((2 : Nat) ^ 84 + (2 : Nat) ^ 84 + 1) * 4) := by
    unfold famTwoEb
    exact cubicBaseExponent_inv_le hw2 (Nat.succ_pos _) hmqs (by positivity) hr8
  have hEr0 : 0 < famTwoEr m qf (rho / 8) := by
    unfold famTwoEr
    exact div_pos (cubicBaseExponent_pos (Nat.succ_pos _) (by positivity)) (by norm_num)
  have hEr : (famTwoEr m qf (rho / 8))⁻¹ ≤
      w ^ (4 + (27 + 4 * 3 + ((2 : Nat) ^ 84 + (2 : Nat) ^ 84 + 1) * 4)) := by
    unfold famTwoEr
    rw [inv_div, div_eq_mul_inv, pow_add]
    exact mul_le_mul (const_le_pow hw2 (by norm_num))
      (cubicBaseExponent_inv_le hw2 (Nat.succ_pos _) hmqf (by positivity) hr8)
      (inv_pos.mpr (cubicBaseExponent_pos (Nat.succ_pos _) (by positivity))).le
      (pow_nonneg hw0 _)
  set L := pieceLineExponent (familyWidthDivisor 1 p1) (famTwoQb m qs) (famTwoEb m qs)
    (famTwoEr m qf) rho with hLdef
  have hLval : L = famTwoEr m qf (rho / 8) * famTwoEb m qs (rho / 8) /
      familyWidthDivisor 1 p1 (3 * (m * qs + 1)) := by
    rw [hLdef]; unfold pieceLineExponent; rw [hfloor]
  have hL0 : 0 < L := by rw [hLval]; positivity
  have hLi : L⁻¹ ≤ w ^ ((2 : Nat) ^ 90) := by
    rw [hLval, inv_div, div_eq_mul_inv, mul_inv]
    have h := mul_le_pow_add hBq0.le
      (mul_nonneg (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le) hBq
      (mul_le_pow_add (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le hEr hEb hw0) hw0
    exact le_pow_mono hw2 (by norm_num) h
  -- the slice exponent
  have hQr := famTwoQr_le_power hw2 hm' hqf' (rho / 8)
  have hSamp := famPieceSamples_le_power (Qr := famTwoQr m qf) hw2 hr hrw hQr hm'
  set Sp := famPieceSamples (famTwoQr m qf) m rho
  have hqS : ((m * (Sp * qf) + 1 : Nat) : Real) ≤
      w ^ ((2 : Nat) ^ 84 + (((2 : Nat) ^ 84 + (2 : Nat) ^ 84 + 5 + (2 : Nat) ^ 84 + 7) +
        (2 : Nat) ^ 84) + 1) := by
    have h := nat_mul_le_pow hw2 hm' (nat_mul_le_pow hw2 hSamp hqf')
    push_cast; push_cast at h
    exact add_le_pow_succ hw2 h (one_le_pow_of_two_le hw2 _)
  set S := famPieceSliceExponent (famTwoQr m qf) (famTwoEs m qf) m rho with hSdef
  have hSval : S = cubicBaseExponent (m * (Sp * qf) + 1) (rho / 4) := by
    rw [hSdef]; rfl
  have hS0 : 0 < S := by rw [hSval]; exact cubicBaseExponent_pos (Nat.succ_pos _) (by positivity)
  have hS1 : S ≤ 1 := by
    rw [hSval]
    exact cubicBaseExponent_le_one (Nat.succ_pos _) (by positivity) (by linarith only [hr1])
  have hSi : S⁻¹ ≤ w ^ ((2 : Nat) ^ 90) := by
    rw [hSval]
    exact le_pow_mono hw2 (by norm_num)
      (cubicBaseExponent_inv_le hw2 (Nat.succ_pos _) hqS (by positivity) hr4)
  -- the scale `z = ζ / A`
  set z := pieceWidthScale (familyWidthPrefactor K1) (famTwoQb m qs) ζ rho with hzdef
  have hA : familyWidthPrefactor K1 (3 * (m * qs + 1)) ≤
      w ^ (2 + (3 + (2 + ((2 : Nat) ^ 84 + (2 : Nat) ^ 84 + 1) + 1))) := by
    unfold familyWidthPrefactor
    rw [Nat.cast_mul, pow_add, pow_add]
    exact mul_le_mul (const_le_pow hw2 (by norm_num))
      (mul_le_mul hK hn1 (Nat.cast_nonneg _) (pow_nonneg hw0 _)) (by positivity)
      (pow_nonneg hw0 _)
  have hA1 : 1 ≤ familyWidthPrefactor K1 (3 * (m * qs + 1)) := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((K1 * (3 * (m * qs + 1) + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  have hzval : z = ζ / familyWidthPrefactor K1 (3 * (m * qs + 1)) := by
    rw [hzdef]; unfold pieceWidthScale; rw [hfloor]
  have hz0 : 0 < z := by rw [hzval]; exact div_pos hζ0 (lt_of_lt_of_le zero_lt_one hA1)
  have hz1 : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact hζ1.trans hA1
  have hzi : z⁻¹ ≤ Real.exp (w ^ ((2 : Nat) ^ 128 + 1)) := by
    rw [hzval, inv_div, div_eq_mul_inv]
    have hAe : familyWidthPrefactor K1 (3 * (m * qs + 1)) ≤ Real.exp (w ^ ((2 : Nat) ^ 128)) :=
      le_exp_pow_of_le_pow (le_pow_mono hw2 (by norm_num) hA)
    calc familyWidthPrefactor K1 (3 * (m * qs + 1)) * ζ⁻¹
        ≤ Real.exp (w ^ ((2 : Nat) ^ 128)) * Real.exp (w ^ ((2 : Nat) ^ 128)) :=
          mul_le_mul hAe hζw (inv_pos.mpr hζ0).le (Real.exp_pos _).le
      _ = Real.exp (w ^ ((2 : Nat) ^ 128) * 2) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (w ^ ((2 : Nat) ^ 128 + 1)) := by
          rw [pow_succ]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw2 (pow_nonneg hw0 _))
  have hcap := capped_rounded_inv_le hw2 (by norm_num) hL0 hLi hS0 hS1 hSi hz0 hz1 hzi
  exact hcap.trans (pow_le_pow_right₀ hw1 (by norm_num))

end LeanProofs.GowersSzemeredi
