import Diophantine.Paper1982.ShortDefs

/-!
# The six block bounds for the shorter coding system in Jones 1982, §5

The third block must be estimated without assuming a sign for `D₀`.
The proof below establishes `|2c⁴D₀| < Q²`, using (D8) and `4z < B`.
Every subtraction in a block is interpreted over `ℤ`.
-/

namespace Jones1982

/-- The six block bounds, with the signed masks and third block kept in `ℤ`. -/
def ShortPackingBounds (z b B c e g l Q lam : ℕ) : Prop :=
  g < Q ∧
  0 ≤ (Q : ℤ) - 1 - ((b : ℤ) - 1) * l ∧
  (Q : ℤ) - 1 - ((b : ℤ) - 1) * l < Q ∧
  l + e * Q < 2 * z * Q ^ 2 ∧
  0 ≤ ((B : ℤ) - 2 * z) * lam * (1 + Q) ∧
  ((B : ℤ) - 2 * z) * lam * (1 + Q) < 2 * z * (Q : ℤ) ^ 2 ∧
  0 < shortS3 z B c e Q lam ∧
  shortS3 z B c e Q lam < 8 * (Q : ℤ) ^ 2 ∧
  0 ≤ ((B : ℤ) - 2) * Q ∧
  ((B : ℤ) - 2) * Q < 8 * (Q : ℤ) ^ 2

set_option maxHeartbeats 1000000 in
/-- Numeric form of the §5 packing bounds; no digit or carry hypothesis is needed. -/
theorem short_packing_bounds {x z b B c e g l Q lam : ℕ}
    (hz : 2 ≤ z) (hb : 2 ≤ b) (h4z : 4 * z < B) (hlam : 0 < lam) (hl : 0 < l)
    (hgeom : Q = 1 + lam * (B - 1)) (hc : c = 1 + x * B + g)
    (hsmall : e + 2 * z * b * l + 2 * z * B * c ^ 4 < 2 * z * Q) :
    ShortPackingBounds z b B c e g l Q lam := by
  have hB2 : 2 ≤ B := by omega
  have hB0 : 0 < B := by omega
  have hbl : b * l < Q := by
    have hmul : 2 * z * (b * l) < 2 * z * Q := by
      calc 2 * z * (b * l) = 2 * z * b * l := by ring
        _ ≤ e + 2 * z * b * l + 2 * z * B * c ^ 4 := by omega
        _ < 2 * z * Q := hsmall
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hBc : B * c ^ 4 < Q := by
    have hmul : 2 * z * (B * c ^ 4) < 2 * z * Q := by
      calc 2 * z * (B * c ^ 4) = 2 * z * B * c ^ 4 := by ring
        _ ≤ e + 2 * z * b * l + 2 * z * B * c ^ 4 := by omega
        _ < 2 * z * Q := hsmall
    exact Nat.lt_of_mul_lt_mul_left hmul
  have he : e < 2 * z * Q := by omega
  have hlQ : l < Q := lt_of_le_of_lt (Nat.le_mul_of_pos_left l (by omega : 0 < b)) hbl
  have hc0 : 0 < c := by omega
  have hgQ : g < Q := by
    calc g ≤ c := by omega
      _ ≤ c ^ 4 := Nat.le_self_pow (by norm_num) c
      _ ≤ B * c ^ 4 := Nat.le_mul_of_pos_left _ hB0
      _ < Q := hBc
  have hQ0 : 0 < Q := by omega
  have hS2 : l + e * Q < 2 * z * Q ^ 2 := by
    have he1 : e + 1 ≤ 2 * z * Q := he
    have hmul := Nat.mul_le_mul_right Q he1
    nlinarith only [hmul, hlQ]
  have hzZ : (2 : ℤ) ≤ z := by exact_mod_cast hz
  have hbZ : (2 : ℤ) ≤ b := by exact_mod_cast hb
  have hBZ : (2 : ℤ) ≤ B := by exact_mod_cast hB2
  have h4zZ : 4 * (z : ℤ) < B := by exact_mod_cast h4z
  have hlamZ : (1 : ℤ) ≤ lam := by exact_mod_cast hlam
  have hlZ : (1 : ℤ) ≤ l := by exact_mod_cast hl
  have hQZ : (0 : ℤ) < Q := by exact_mod_cast hQ0
  have hcZ : (0 : ℤ) < c := by exact_mod_cast hc0
  have hblZ : (b : ℤ) * l < Q := by exact_mod_cast hbl
  have hBcZ : (B : ℤ) * c ^ 4 < Q := by exact_mod_cast hBc
  have heZ : (e : ℤ) < 2 * z * Q := by exact_mod_cast he
  have hgeomZ : (Q : ℤ) = 1 + lam * ((B : ℤ) - 1) := by
    have heq := congrArg (fun n : ℕ => (n : ℤ)) hgeom
    push_cast [Nat.cast_sub (by omega : 1 ≤ B)] at heq
    exact heq
  have hlamB : (0 : ℤ) ≤ ((lam : ℤ) - 1) * ((B : ℤ) - 1) := by
    exact mul_nonneg (by omega) (by omega)
  have hQB : (B : ℤ) ≤ Q := by nlinarith only [hgeomZ, hlamB]
  have hQBlam : (Q : ℤ) ≤ B * lam := by nlinarith only [hgeomZ, hlamZ]
  have hprod : (0 : ℤ) ≤ lam * ((B : ℤ) - 2) := by
    exact mul_nonneg (by omega) (by omega)
  have hlamQ : (lam : ℤ) < Q := by nlinarith only [hgeomZ, hprod]
  have hBlam : (B : ℤ) * lam + 1 < 2 * Q := by
    nlinarith only [hgeomZ, hprod, hlamZ]
  let D₀ : ℤ := z * ((lam : ℤ) + Q) - e
  let mask : ℤ := (B : ℤ) * lam * (1 + Q)
  have hDabs : |D₀| < 2 * (z : ℤ) * Q := by
    have htop : (z : ℤ) * (lam + Q) < 2 * z * Q := by
      have h := mul_lt_mul_of_pos_left hlamQ (by omega : (0 : ℤ) < z)
      nlinarith only [h]
    have hzero : (0 : ℤ) ≤ z * (lam + Q) := by positivity
    rw [abs_lt]
    dsimp [D₀]
    constructor <;> nlinarith only [htop, hzero, heZ, Int.natCast_nonneg e]
  have h4zc : 4 * (z : ℤ) * c ^ 4 < Q := by
    have h := mul_lt_mul_of_pos_right h4zZ (pow_pos hcZ 4)
    exact h.trans hBcZ
  have herr : |2 * (c : ℤ) ^ 4 * D₀| < (Q : ℤ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * c ^ 4)]
    calc 2 * (c : ℤ) ^ 4 * |D₀| < 2 * c ^ 4 * (2 * z * Q) :=
        mul_lt_mul_of_pos_left hDabs (by positivity)
      _ = (4 * z * c ^ 4) * Q := by ring
      _ < (Q : ℤ) * Q := mul_lt_mul_of_pos_right h4zc hQZ
      _ = (Q : ℤ) ^ 2 := by ring
  have hmaskLower : (Q : ℤ) ^ 2 ≤ mask := by
    have h := mul_le_mul_of_nonneg_right hQBlam hQZ.le
    have hnonneg : (0 : ℤ) ≤ B * lam := by positivity
    dsimp [mask]
    nlinarith only [h, hnonneg]
  have hmaskUpper : mask < 4 * (Q : ℤ) ^ 2 := by
    dsimp [mask]
    calc (B : ℤ) * lam * (1 + Q) < 2 * Q * (1 + Q) :=
        mul_lt_mul_of_pos_right (by linarith only [hBlam]) (by omega)
      _ ≤ 2 * Q * (2 * Q) :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      _ = 4 * (Q : ℤ) ^ 2 := by ring
  have hS3eq : shortS3 z B c e Q lam = mask - 2 * (c : ℤ) ^ 4 * D₀ := by
    dsimp [shortS3, mask, D₀]
    ring
  have hQsq : (0 : ℤ) < (Q : ℤ) ^ 2 := pow_pos hQZ 2
  have hS3pos : 0 < shortS3 z B c e Q lam := by
    rw [hS3eq]
    have h := (abs_lt.mp herr).2
    linarith only [hmaskLower, h]
  have hS3lt : shortS3 z B c e Q lam < 8 * (Q : ℤ) ^ 2 := by
    rw [hS3eq]
    have h := (abs_lt.mp herr).1
    linarith only [hmaskUpper, h, hQsq]
  have hT2mask : ((B : ℤ) - 2 * z) * lam * (1 + Q) ≤ mask := by
    dsimp [mask]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by omega) (by positivity)) (by positivity)
  have hT2lt : ((B : ℤ) - 2 * z) * lam * (1 + Q) < 2 * z * (Q : ℤ) ^ 2 := by
    calc _ ≤ mask := hT2mask
      _ < 4 * (Q : ℤ) ^ 2 := hmaskUpper
      _ ≤ 2 * z * (Q : ℤ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by omega) (by positivity)
  have hT3lt : ((B : ℤ) - 2) * Q < 8 * (Q : ℤ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hQB hQZ.le
    nlinarith only [h, hQZ, hQsq]
  have hmask1prod : (0 : ℤ) ≤ ((b : ℤ) - 1) * l :=
    mul_nonneg (by omega) (by positivity)
  refine ⟨hgQ, ?_, ?_, hS2, ?_, hT2lt, hS3pos, hS3lt, ?_, hT3lt⟩
  · nlinarith only [hblZ, hlZ]
  · linarith only [hmask1prod]
  · exact mul_nonneg (mul_nonneg (by omega) (by positivity)) (by positivity)
  · exact mul_nonneg (by omega) hQZ.le

/-- The base chosen in (D2) satisfies the estimate needed for the third block. -/
theorem shortBase_four_z_lt (ν : ℕ) {z b : ℕ} (hz : 2 ≤ z) (hb : 2 ≤ b) :
    4 * z < shortBase ν z b := by
  have hb4 : 2 ≤ b ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hb 4)
  have hpow : 2 * z ≤ (2 * z) ^ (L4 ν + 1) := Nat.le_self_pow (by omega) _
  unfold shortBase
  calc 4 * z < 4 * (2 * z) := by omega
    _ ≤ 2 * b ^ 4 * (2 * z) := by nlinarith only [hb4, hz]
    _ ≤ 2 * b ^ 4 * (2 * z) ^ (L4 ν + 1) := Nat.mul_le_mul_left _ hpow

/-- The actual shorter coding equations imply all six strict block bounds. -/
theorem ShortEqs.packing_bounds {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ}
    {x z u y b B c e g l m Q t lam ε : ℕ}
    (hI : Index ν P z u y) (hx : 0 < x) (hε : 0 < ε) (hl : 0 < l)
    (h : ShortEqs ν x z u y b B c e g l m Q t lam ε) :
    ShortPackingBounds z b B c e g l Q lam := by
  have hz := hI.two_le
  have hb : 2 ≤ b := by have := h.D1; omega
  have h4z : 4 * z < B := by rw [h.D2]; exact shortBase_four_z_lt ν hz hb
  have hB : 2 ≤ B := by omega
  have hL : 1 ≤ L4 ν := by
    change 1 ≤ 5 ^ (ν + 1)
    exact Nat.one_le_pow _ _ (by norm_num)
  have hBQ : B ≤ Q := by
    rw [h.power]
    calc B = B ^ 1 := by simp
      _ ≤ B ^ L4 ν := Nat.pow_le_pow_right (by omega) hL
  have hlam : 0 < lam := by
    have hg := h.D7
    by_contra hn
    have : lam = 0 := by omega
    rw [this, zero_mul, add_zero] at hg
    omega
  exact short_packing_bounds hz hb h4z hlam hl h.D7 h.D6 h.D8

end Jones1982
