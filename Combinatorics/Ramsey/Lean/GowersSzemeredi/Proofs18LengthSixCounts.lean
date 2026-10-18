import GowersSzemeredi.Proofs18LengthSixScale
import GowersSzemeredi.Proofs16BaseFamilyPowerBound
import GowersSzemeredi.Proofs16PolyFamilyTwo

/-! Polynomial bounds on the graph counts of the length-six route.

The density `β` of the final discrepancy bound depends only on the graph
counts `sixQb` (through the lift densities `sixC`), not on the width
exponents. Here every count is bounded by a power of
`u = 2/(γ θ ρ)`:
* `section16BaseFamilyBound γ θ ≤ u^(2^14)`;
* Lemma 15.6's threshold, the piece count `polyTwoPieces` and the face
  count `polyPieceFaceCount` by explicit powers;
* `sixQb l γ θ ρ ≤ (2/(γθρ))^(2^90)` (`sixQb_le_power`).
The last two items are in `Proofs18LengthSixCountsSide`, outside the final
route.

Degrees are kept as powers of two, so the final comparison only adds
exponents. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Power calculus -/

/-- `y ≤ x^a`, `z ≤ x^b` give `y z ≤ x^(a+b)`. -/
theorem mul_le_pow_add {x y z : Real} {a b : Nat} (hz0 : 0 ≤ z)
    (hy : y ≤ x ^ a) (hz : z ≤ x ^ b) (hx : 0 ≤ x) : y * z ≤ x ^ (a + b) := by
  rw [pow_add]
  exact mul_le_mul hy hz hz0 (pow_nonneg hx _)

/-- A sum of two powers is below the next power, for `x ≥ 2`. -/
theorem add_le_pow_succ {x y z : Real} {a : Nat} (hx : 2 ≤ x) (hy : y ≤ x ^ a) (hz : z ≤ x ^ a) :
    y + z ≤ x ^ (a + 1) := by
  rw [pow_succ]
  have h := pow_nonneg (show (0 : Real) ≤ x by linarith) a
  nlinarith

/-- `⌈y⌉ ≤ x^(a+1)` when `0 ≤ y ≤ x^a` and `x ≥ 2`. -/
theorem ceil_le_pow_succ {x y : Real} {a : Nat} (hx : 2 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ x ^ a) :
    (⌈y⌉₊ : Real) ≤ x ^ (a + 1) := by
  have h1 : (⌈y⌉₊ : Real) ≤ y + 1 := (Nat.ceil_lt_add_one hy0).le
  have h2 : (1 : Real) ≤ x ^ a := one_le_pow₀ (by linarith)
  exact h1.trans (add_le_pow_succ hx hy h2)

/-! ### The base family bound -/

/-- `section16BaseFamilyBound γ θ ≤ (2/(γθ))^(2^14)`, from the sharper
`section16BaseFamilyBound_le_power` (exponent `10002`). -/
theorem section16BaseFamilyBound_le_dyadic_power {gamma theta : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16BaseFamilyBound gamma theta : Real) ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 14) := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hu1 : 1 ≤ 2 / (gamma * theta) := by
    rw [le_div_iff₀ hgt]; nlinarith [mul_le_one₀ hg1 ht.le ht1]
  exact (section16BaseFamilyBound_le_power hg hg1 ht ht1).trans
    (pow_le_pow_right₀ hu1 (by norm_num))

/-! ### The piece budget, the face count and the piece count

Trap: `linarith` (through `cancel_denoms`) evaluates `1 ^ n` as a runtime
`Nat.pow` for every power atom `x ^ n` in the context, which panics once
`n ≥ 2^24`. Every arithmetic fact below is therefore derived before the
first hypothesis with a huge exponent enters the context. -/

/-- The elementary facts about `u = 2/(γθ)` for `γ, θ ∈ (0, 1]`. -/
theorem prod_scale_basic {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    2 ≤ 2 / (gamma * theta) ∧ gamma⁻¹ ≤ 2 / (gamma * theta) ∧
      2 / gamma ≤ 2 / (gamma * theta) ∧ (2 / (gamma * theta))⁻¹ ≤ theta / 2 ∧
      (2 / (gamma * theta))⁻¹ ≤ gamma := by
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
  have hgg : gamma * theta ≤ gamma := by nlinarith
  have hinv : (2 / (gamma * theta))⁻¹ = gamma * theta / 2 := by rw [inv_div]
  refine ⟨by rw [le_div_iff₀ hgt]; linarith, ?_, ?_, ?_, ?_⟩
  · rw [div_eq_mul_inv]
    have : gamma⁻¹ ≤ (gamma * theta)⁻¹ := inv_anti₀ hgt hgg
    linarith [inv_pos.mpr hgt]
  · exact div_le_div_of_nonneg_left (by norm_num) hgt hgg
  · rw [hinv]; nlinarith
  · rw [hinv]; nlinarith

/-- Extending the product scale by a radius at most one controls both previous scales. -/
theorem prod_scale_radius_bounds {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) :
    2 ≤ 2 / (gamma * theta) ∧ 2 / (gamma * theta) ≤ 2 / (gamma * theta * rho) ∧
      rho⁻¹ ≤ 2 / (gamma * theta * rho) := by
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hgt : 0 < gamma * theta := mul_pos hg ht
  have hvw : 2 / (gamma * theta) ≤ 2 / (gamma * theta * rho) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hgt hr) (mul_le_of_le_one_right hgt.le hr1)
  refine ⟨hv2, hvw, ?_⟩
  rw [show 2 / (gamma * theta * rho) = 2 / (gamma * theta) * rho⁻¹ by field_simp]
  exact le_mul_of_one_le_left (inv_pos.mpr hr).le (one_le_two.trans hv2)

/-- `(γθ/4) ≥ u⁻²` for `u = 2/(γθ) ≥ 2`. -/
theorem quarter_prod_ge_inv_sq {gamma theta : Real} (hg : 0 < gamma) (ht : 0 < theta)
    (hu2 : 2 ≤ 2 / (gamma * theta)) :
    ((2 / (gamma * theta)) ^ 2)⁻¹ ≤ theta * gamma / 4 := by
  have heq : theta * gamma / 4 = (2 * (2 / (gamma * theta)))⁻¹ := by
    field_simp; ring
  rw [heq]
  exact inv_anti₀ (by positivity) (by nlinarith)

theorem polyPieceBudget_ge_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ((2 / (gamma * theta)) ^ ((2 : Nat) ^ 69))⁻¹ ≤ polyPieceBudget theta gamma := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := quarter_prod_ge_inv_sq hg ht hu2
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hu1 : 1 ≤ u := by linarith
  have hupos : 0 < u := by linarith
  have h35 : (u ^ 35)⁻¹ ≤ (2 : Real) ^ (-(32 : Real)) / 8 := by
    have h1 : (2 : Real) ^ (-(32 : Real)) / 8 = ((2 : Real) ^ 35)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
      norm_num
    rw [h1]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hu2 35)
  -- θ₁ ≥ u^(-2^65)
  have hθ1 : (u ^ ((2 : Nat) ^ 65))⁻¹ ≤ section16ThetaOne theta gamma 1 := by
    unfold section16ThetaOne
    have h := pow_le_pow_left₀ (by positivity) hq ((2 : Nat) ^ ((2 : Nat) ^ (1 + 5)))
    rw [inv_pow, ← pow_mul] at h
    refine le_trans ?_ h
    apply inv_anti₀ (pow_pos hupos _)
    apply pow_le_pow_right₀ hu1
    norm_num
  have hθ18 : (u ^ ((2 : Nat) ^ 68))⁻¹ ≤ section16ThetaOne theta gamma 1 ^ 8 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr (pow_pos hupos _).le) hθ1 8
    rw [inv_pow, ← pow_mul] at h
    refine le_trans ?_ h
    apply inv_anti₀ (pow_pos hupos _)
    apply pow_le_pow_right₀ hu1
    norm_num
  unfold polyPieceBudget section16ThetaTwo
  calc (u ^ ((2 : Nat) ^ 69))⁻¹ ≤ (u ^ 35 * u ^ ((2 : Nat) ^ 68))⁻¹ := by
        apply inv_anti₀ (mul_pos (pow_pos hupos _) (pow_pos hupos _))
        rw [← pow_add]
        apply pow_le_pow_right₀ hu1
        norm_num
    _ = (u ^ 35)⁻¹ * (u ^ ((2 : Nat) ^ 68))⁻¹ := mul_inv _ _
    _ ≤ (2 : Real) ^ (-(32 : Real)) / 8 * section16ThetaOne theta gamma 1 ^ 8 :=
        mul_le_mul h35 hθ18 (inv_nonneg.mpr (pow_pos hupos _).le) (by positivity)
    _ = (2 : Real) ^ (-(32 : Real)) * section16ThetaOne theta gamma 1 ^ 8 / 8 := by ring

/-- `θ′⁻¹ ≤ (2/(γθ))^(2^69)` for the piece budget `θ′`. -/
theorem polyPieceBudget_inv_le_power {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceBudget theta gamma)⁻¹ ≤ (2 / (gamma * theta)) ^ ((2 : Nat) ^ 69) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hupos : 0 < 2 / (gamma * theta) := by linarith
  have h := polyPieceBudget_ge_power hg hg1 ht ht1
  have := inv_anti₀ (inv_pos.mpr (pow_pos hupos _)) h
  rwa [inv_inv] at this

/-! ### The family count

Below `w ≥ 2` is an abstract base; every count is bounded by `w^e` with an
explicit `e`, and only the power rules are used (no `linarith`, see the
trap above). -/

theorem le_pow_mono {w y : Real} {a b : Nat} (hw : 2 ≤ w) (hab : a ≤ b) (hy : y ≤ w ^ a) :
    y ≤ w ^ b :=
  hy.trans (pow_le_pow_right₀ (le_trans (by norm_num) hw) hab)

/-- A numerical constant `c ≤ 2^j` costs `j` in the exponent. -/
theorem const_mul_le_pow {w c y : Real} {a j : Nat} (hw : 2 ≤ w) (_hc0 : 0 ≤ c) (hc : c ≤ 2 ^ j)
    (hy0 : 0 ≤ y) (hy : y ≤ w ^ a) : c * y ≤ w ^ (j + a) := by
  rw [pow_add]
  exact mul_le_mul (hc.trans (pow_le_pow_left₀ (by norm_num) hw j)) hy hy0
    (pow_nonneg (le_trans (by norm_num) hw) _)

theorem nat_mul_le_pow {w : Real} {m n : Nat} {a b : Nat} (hw : 2 ≤ w) (hm : (m : Real) ≤ w ^ a)
    (hn : (n : Real) ≤ w ^ b) : ((m * n : Nat) : Real) ≤ w ^ (a + b) := by
  push_cast
  exact mul_le_pow_add (Nat.cast_nonneg _) hm hn (le_trans (by norm_num) hw)

/-- `c (m n + 1)` for a constant `c ≤ 2^j`. -/
theorem nat_affine_le_pow {w : Real} {c m n : Nat} {a b j : Nat} (hw : 2 ≤ w) (hc : (c : Real) ≤ 2 ^ j)
    (hm : (m : Real) ≤ w ^ a) (hn : (n : Real) ≤ w ^ b) :
    ((c * (m * n + 1) : Nat) : Real) ≤ w ^ (j + (a + b + 1)) := by
  have hmn := nat_mul_le_pow hw hm hn
  have h1 : (1 : Real) ≤ w ^ (a + b) := one_le_pow₀ (le_trans (by norm_num) hw)
  have hs : ((m * n + 1 : Nat) : Real) ≤ w ^ (a + b + 1) := by
    push_cast
    push_cast at hmn
    exact add_le_pow_succ hw hmn h1
  rw [Nat.cast_mul]
  exact const_mul_le_pow hw (Nat.cast_nonneg _) hc (Nat.cast_nonneg _) hs

/-- The sample count from separate family-size and parameter bases. -/
theorem famPieceSamples_le_two_bases {ν w rho : Real} {Qr : Real → Real}
    {n a b c d : Nat} (hν : 1 ≤ ν) (hw : 2 ≤ w) (hrho : 0 < rho) (hrw : rho⁻¹ ≤ w)
    (hQ : Qr (rho / 8) ≤ ν ^ a * w ^ b) (hn : (n : Real) ≤ ν ^ c * w ^ d) :
    (famPieceSamples Qr n rho : Real) ≤ ν ^ (a + c) * w ^ (b + d + 7) := by
  have hw1 : 1 ≤ w := by linarith only [hw]
  have hQ1 : max 1 (Qr (rho / 8)) ≤ ν ^ a * w ^ b :=
    max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hν) (one_le_pow₀ hw1)) hQ
  have hn1 : ((max 1 n : Nat) : Real) ≤ ν ^ c * w ^ d := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hν) (one_le_pow₀ hw1)) hn
  set X := ν ^ (a + c) * w ^ (b + d + 1) with hXdef
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hν) (one_le_pow₀ hw1)
  have hprod : max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) * rho⁻¹ ≤ X := by
    have h := mul_le_mul (mul_le_mul hQ1 hn1 (Nat.cast_nonneg _) (by positivity))
      hrw (inv_pos.mpr hrho).le (by positivity)
    exact h.trans_eq (by rw [hXdef]; ring)
  have h25 : (25 : Real) ≤ w ^ 6 :=
    (by norm_num : (25 : Real) ≤ 2 ^ 6).trans (pow_le_pow_left₀ (by norm_num) hw 6)
  unfold famPieceSamples
  calc (⌈6 * max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) / (rho / 4)⌉₊ : Real)
      ≤ 6 * max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) / (rho / 4) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
    _ = 24 * (max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) * rho⁻¹) + 1 := by field_simp; ring
    _ ≤ 25 * X := by nlinarith only [hprod, hX1]
    _ ≤ w ^ 6 * X := mul_le_mul_of_nonneg_right h25 (zero_le_one.trans hX1)
    _ = ν ^ (a + c) * w ^ (b + d + 7) := by rw [hXdef]; ring

/-- The sample count of the family piece cover. -/
theorem famPieceSamples_le_power {w rho : Real} {Qr : Real → Real} {n a b : Nat} (hw : 2 ≤ w)
    (hrho : 0 < rho) (hrw : rho⁻¹ ≤ w) (hQ : Qr (rho / 8) ≤ w ^ a) (hn : (n : Real) ≤ w ^ b) :
    (famPieceSamples Qr n rho : Real) ≤ w ^ (a + b + 7) := by
  simpa using famPieceSamples_le_two_bases (ν := 1) (a := 0) (b := a) (c := 0) (d := b)
    (by norm_num) hw hrho hrw (by simpa using hQ) (by simpa using hn)

/-- A graph-count bound from separate bounds on the family, samples and slices. -/
theorem famPieceGraphBound_le_mul_sq {N S B rho : Real} {Qr : Real → Real}
    {Pb : Nat → Real → Real} {n : Nat} (hS1 : 1 ≤ S) (hB1 : 1 ≤ B)
    (hn : (n : Real) ≤ N) (hS : (famPieceSamples Qr n rho : Real) ≤ S)
    (hP0 : 0 ≤ Pb (famPieceSamples Qr n rho) (rho / 4))
    (hP : Pb (famPieceSamples Qr n rho) (rho / 4) ≤ B) :
    famPieceGraphBound Qr Pb n rho ≤ N * (S ^ 2 * B ^ 2) := by
  set s := famPieceSamples Qr n rho
  set p := Pb s (rho / 4)
  have hchoose : ((s.choose 2 : Nat) : Real) ≤ S ^ 2 := by
    calc ((s.choose 2 : Nat) : Real) ≤ (s : Real) ^ 2 := by exact_mod_cast Nat.choose_le_pow s 2
      _ ≤ S ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hS 2
  have hmax : max p (((s.choose 2 : Nat) : Real) * p * p) ≤ S ^ 2 * B ^ 2 := by
    refine max_le (hP.trans ((le_self_pow₀ hB1 (by decide : (2 : Nat) ≠ 0)).trans
      (le_mul_of_one_le_left (sq_nonneg B) (one_le_pow₀ hS1)))) ?_
    rw [mul_assoc, ← sq]
    exact mul_le_mul hchoose (pow_le_pow_left₀ hP0 hP 2) (sq_nonneg p) (sq_nonneg S)
  unfold famPieceGraphBound
  exact mul_le_mul hn hmax (hP0.trans (le_max_left _ _)) ((Nat.cast_nonneg n).trans hn)

/-- The family graph count, from bounds on the samples, the slice count and `n`. -/
theorem famPieceGraphBound_le_power {w rho : Real} {Qr : Real → Real} {Pb : Nat → Real → Real}
    {n b s c : Nat} (hw : 2 ≤ w) (hn : (n : Real) ≤ w ^ b)
    (hS : (famPieceSamples Qr n rho : Real) ≤ w ^ s)
    (hP0 : 0 ≤ Pb (famPieceSamples Qr n rho) (rho / 4))
    (hP : Pb (famPieceSamples Qr n rho) (rho / 4) ≤ w ^ c) :
    famPieceGraphBound Qr Pb n rho ≤ w ^ (b + (2 * s + c + c)) := by
  have hw1 : 1 ≤ w := by linarith only [hw]
  have h := famPieceGraphBound_le_mul_sq (one_le_pow₀ hw1) (one_le_pow₀ hw1) hn hS hP0 hP
  convert h using 1 <;> ring

/-- `famTwoQr m q ≤ w^(a+b+5)`. -/
theorem famTwoQr_le_power {w : Real} {m q a b : Nat} (hw : 2 ≤ w) (hm : (m : Real) ≤ w ^ a)
    (hq : (q : Real) ≤ w ^ b) (t : Real) : famTwoQr m q t ≤ w ^ (a + b + 5) := by
  unfold famTwoQr
  apply max_le
  · exact le_pow_mono hw (by omega) (nat_affine_le_pow (c := 3) (j := 2) hw (by norm_num) hm hq)
  · exact le_pow_mono hw (by omega)
      (nat_affine_le_pow (c := 3 ^ (1 + 1)) (j := 4) hw (by norm_num) hm hq)

/-- `famTwoPb m q r ≤ w^(a+(s+b)+3)` for `r ≤ w^s`. -/
theorem famTwoPb_le_power {w : Real} {m q r a b s : Nat} (hw : 2 ≤ w) (hm : (m : Real) ≤ w ^ a)
    (hq : (q : Real) ≤ w ^ b) (hr : (r : Real) ≤ w ^ s) (t : Real) :
    famTwoPb m q r t ≤ w ^ (2 + (a + (s + b) + 1)) := by
  unfold famTwoPb
  exact nat_affine_le_pow (c := 3) (j := 2) hw (by norm_num) hm (nat_mul_le_pow hw hr hq)

/-- The dimension-two family count is polynomial in its piece and face counts. -/
theorem famTwoCount_le_power {w rho : Real} {m q a b : Nat} (hw : 2 ≤ w)
    (hr : 0 < rho) (hrw : rho⁻¹ ≤ w) (hm : (m : Real) ≤ w ^ a) (hq : (q : Real) ≤ w ^ b) :
    max (famPieceGraphBound (famTwoQr m q) (famTwoPb m q) m rho)
      ((3 ^ (1 + 1) * m : Nat) : Real) ≤ w ^ (11 * a + 6 * b + 54) := by
  have hQr := famTwoQr_le_power hw hm hq (rho / 8)
  have hS := famPieceSamples_le_power (Qr := famTwoQr m q) hw hr hrw hQr hm
  have hP := famTwoPb_le_power hw hm hq hS (rho / 4)
  have hP0 : 0 ≤ famTwoPb m q (famPieceSamples (famTwoQr m q) m rho) (rho / 4) := by
    unfold famTwoPb; exact Nat.cast_nonneg _
  have hG := famPieceGraphBound_le_power (Pb := famTwoPb m q) hw hm hS hP0 hP
  refine max_le (hG.trans_eq (by congr 1 <;> omega)) ?_
  have h9 : ((3 ^ (1 + 1) * m : Nat) : Real) ≤ w ^ (4 + a) := by
    rw [Nat.cast_mul]
    exact const_mul_le_pow hw (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) hm
  exact le_pow_mono hw (by omega) h9

end LeanProofs.GowersSzemeredi
