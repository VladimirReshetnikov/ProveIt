import DiophantineConsistency.PolynomialRangeBounds

/-! # Package 52's base, cap and cofinal witness bounds

These arithmetic bounds are independent of the source predicate and of any
native coefficient calibration. The cofinal power of two is explicit data.
-/

namespace DiophantineConsistency.NativeBaseBounds52

open scoped BigOperators

def base (H b : ℕ) : ℕ := 4096 * H * b ^ 2

def cap (B b : ℕ) : ℕ := 32 * b * B ^ 174

def packedBase (B : ℕ) : ℕ := 4 * B ^ 8040

theorem base_gt_four_digits {H b : ℕ} (hH : 0 < H) (hb : 0 < b) :
    4 * b < base H b := by
  have h := PolynomialRangeBounds.scale_gt_four_digits
    (show (0 : ℤ) < H by exact_mod_cast hH)
    (show (1 : ℤ) ≤ b by exact_mod_cast hb)
  exact_mod_cast h

theorem base_bounds {H b : ℕ} (hH : 0 < H) (hb : 0 < b) :
    2 ≤ base H b ∧ b < base H b := by
  have h := base_gt_four_digits hH hb
  omega

theorem weak_cap_of_ratio {B b g : ℕ} (hg : 8 * g < cap B b) :
    g < 4 * b * B ^ 174 := by
  unfold cap at hg
  nlinarith only [hg]

theorem strong_cap_of_code {B b g : ℕ} (hg : g < b * B ^ 174) :
    32 * g < cap B b := by
  unfold cap
  nlinarith only [hg]

theorem cap_pos {B b : ℕ} (hB : 0 < B) (hb : 0 < b) : 0 < cap B b := by
  unfold cap
  positivity

theorem packedBase_eq (B : ℕ) : B ^ 175 * (4 * B ^ 7865) = packedBase B := by
  rw [packedBase, ← mul_assoc, mul_comm (B ^ 175) 4, mul_assoc, ← pow_add]

theorem packedBase_bounds {B b : ℕ} (hB : 2 ≤ B) (hbB : b ≤ B) :
    8 ≤ packedBase B ∧ b ≤ packedBase B := by
  have hp : B ≤ B ^ 8040 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by omega : 1 ≤ B) (by decide : 1 ≤ 8040))
  unfold packedBase
  constructor <;> omega

theorem base_power (a k : ℕ) : base (2 ^ a) (2 ^ k) = 2 ^ (a + 12 + 2 * k) := by
  unfold base
  have hc : (4096 : ℕ) = 2 ^ 12 := by decide
  rw [hc, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

/-- The published height gives exactly the published power-of-two scale. -/
theorem published_base_power (k : ℕ) :
    base (2 ^ 1182955) (2 ^ k) = 2 ^ (1182967 + 2 * k) := by
  simpa only [show 1182955 + 12 = 1182967 by decide] using base_power 1182955 k

def cofinalExponent {n : ℕ} (lower : ℕ) (x : Fin n → ℕ) : ℕ :=
  lower + (∑ i, x i) + 1

def cofinalBound {n : ℕ} (lower : ℕ) (x : Fin n → ℕ) : ℕ :=
  2 ^ cofinalExponent lower x

theorem cofinalBound_spec {n : ℕ} (lower : ℕ) (x : Fin n → ℕ) :
    lower < cofinalBound lower x ∧ (∀ i, x i < cofinalBound lower x) ∧
      0 < cofinalBound lower x := by
  have hpow := (cofinalExponent lower x).lt_two_pow_self
  have hlower : lower ≤ cofinalExponent lower x := by unfold cofinalExponent; omega
  have hx : ∀ i, x i ≤ cofinalExponent lower x := by
    intro i
    have hi : x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => Nat.zero_le (x j))
      (Finset.mem_univ i)
    unfold cofinalExponent
    omega
  exact ⟨lt_of_le_of_lt hlower hpow, fun i => lt_of_le_of_lt (hx i) hpow,
    by unfold cofinalBound; positivity⟩

end DiophantineConsistency.NativeBaseBounds52
