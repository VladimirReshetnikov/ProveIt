import Diophantine.Paper1980.Digits93

/-!
# Reading the first and third masks digit by digit (Section 4)

With `q = B^L`, `B = 2^mB`, `b < B` and `l = ℓ₀(B) = Σ_{h<L} ind h · B^h`:

* the first mask `q² − 1 − b l` has base-`B` digit `B − 1` off the indicator
  support and `B − 1 − b` on it (`mask_digit`); hence the first packed
  condition `g & (q² − 1 − b l) = 0` forces every digit of `g` off the support
  to vanish and every digit on the support to be disjoint from `B − 1 − b`
  (`g_digits`), so that `g` is the sum of its digits over the support
  (`g_eq_sum_supp`), i.e. `x + g = C(B)` for the digit polynomial with the
  coordinates `zᵢ = digit_{vᵢ}(g)` and the dummies `digit_{t_j+e}(g)`
  (`C_eq_eval`);
* the third mask `θ l = (B − 4) ℓ₀(B)` has digit `B − 4` on the support and
  `0` off it, so `σ & θ l = 0` bounds every digit of `σ` on the support by
  three (`sigma_digits_le_three`).
-/

namespace Jones1980

namespace Iso

open Layout Finset Polynomial

section Mask

variable {m s : ℕ}

/-- The sum over the indicator support splits into the coordinate weights and the tested
positions. -/
theorem sum_supp {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ supp m s, f i =
      ∑ i : Fin m, f (v i) + ∑ j : Fin s, ∑ e : Fin 3, f (t m s j + e) := by
  unfold supp
  have hdisj : Disjoint ((range m).image v)
      ((range s).biUnion fun j => {t m s j, t m s j + 1, t m s j + 2}) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_image] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    rw [Finset.mem_biUnion] at hb
    obtain ⟨j, _, hj⟩ := hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    have := v_le_M (Finset.mem_range.1 hi); have := t_ge_two_M m s j
    omega
  rw [Finset.sum_union hdisj, Finset.sum_image (fun i _ k _ h => v_strictMono.injective h),
    Finset.sum_range, Finset.sum_biUnion, Finset.sum_range]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton,
      Fin.sum_univ_three]
    simp [add_assoc]
  · intro j hj k hk hjk
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    have := d0_gt m
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · have := t_sub_ge (m := m) (s := s) h; omega
    · have := t_sub_ge (m := m) (s := s) h; omega

variable {B L b q l : ℕ}

/-- `ℓ₀(B)` extended to `2L` digits. -/
theorem ell0_sum_extend (hKL : K m s ≤ L) :
    ∑ h ∈ range L, ind m s h * B ^ h = ∑ h ∈ range (2 * L), ind m s h * B ^ h := by
  apply Finset.sum_subset (Finset.range_mono (show L ≤ 2 * L by omega))
  intro h _ hh
  rw [Finset.mem_range] at hh
  rw [ind_eq_zero_of_ge (show K m s ≤ h by omega), zero_mul]

/-- The first mask as a digit sum. -/
theorem mask_eq (hB : 1 ≤ B) (hb : b < B) (hKL : K m s ≤ L)
    (hl : l = ∑ h ∈ range L, ind m s h * B ^ h) (hq : q = B ^ L) :
    q ^ 2 - 1 - b * l = ∑ i ∈ range (2 * L), (B - 1 - b * ind m s i) * B ^ i := by
  have h1 : q ^ 2 - 1 = ∑ i ∈ range (2 * L), (B - 1) * B ^ i := by
    have := sum_pred_mul_pow hB (2 * L)
    rw [hq, ← pow_mul, mul_comm L 2]; omega
  have h2 : b * l = ∑ i ∈ range (2 * L), b * ind m s i * B ^ i := by
    rw [hl, ell0_sum_extend hKL, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h1, h2, ← Finset.sum_tsub_distrib]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Nat.sub_mul (B - 1) (b * ind m s i) (B ^ i)]
  · intro i _
    have := ind_le_one m s i
    have : b * ind m s i ≤ B - 1 := by
      calc b * ind m s i ≤ b * 1 := Nat.mul_le_mul_left _ this
        _ ≤ B - 1 := by omega
    exact Nat.mul_le_mul_right _ this

/-- The digit of the first mask at `i < 2L` is `B − 1 − b · ind i`. -/
theorem mask_digit (hB : 1 ≤ B) (hb : b < B) (hKL : K m s ≤ L)
    (hl : l = ∑ h ∈ range L, ind m s h * B ^ h) (hq : q = B ^ L) {i : ℕ} (hi : i < 2 * L) :
    (q ^ 2 - 1 - b * l) / B ^ i % B = B - 1 - b * ind m s i := by
  rw [mask_eq hB hb hKL hl hq, digit_sum (by omega) i _ (fun i => by omega), if_pos hi]

/-- The third mask `θ l` as a digit sum. -/
theorem theta_mask_digit (hB : 4 ≤ B) (hKL : K m s ≤ L) {θ : ℕ} (hθ : θ = B - 4)
    (hl : l = ∑ h ∈ range L, ind m s h * B ^ h) {i : ℕ} (hi : i < 2 * L) :
    θ * l / B ^ i % B = (B - 4) * ind m s i := by
  have h : θ * l = ∑ i ∈ range (2 * L), (B - 4) * ind m s i * B ^ i := by
    rw [hl, ell0_sum_extend hKL, Finset.mul_sum, hθ]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h, digit_sum (by omega) i _ (fun i => by
    have := ind_le_one m s i
    calc (B - 4) * ind m s i ≤ (B - 4) * 1 := Nat.mul_le_mul_left _ this
      _ < B := by omega), if_pos hi]

/-- The digits of a base-`2^mB` number, written with `B = 2^mB`. -/
theorem digit_pow_two {mB : ℕ} (hBm : B = 2 ^ mB) (X i : ℕ) :
    X / 2 ^ (mB * i) % 2 ^ mB = X / B ^ i % B := by
  rw [hBm, ← pow_mul]

/-- Reading the first mask: off the support the digits of `g` vanish, on the support they
are disjoint from `B − 1 − b`. -/
theorem g_digits {mB g : ℕ} (hmB : 0 < mB) (hBm : B = 2 ^ mB) (hb : b < B) (hKL : K m s ≤ L)
    (hl : l = ∑ h ∈ range L, ind m s h * B ^ h) (hq : q = B ^ L)
    (hmask : Jones1982.τ 2 g (q ^ 2 - 1 - b * l) = 0) :
    ∀ i < L, (i ∉ supp m s → g / B ^ i % B = 0) ∧
      (i ∈ supp m s → (g / B ^ i % B) &&& (B - 1 - b) = 0) := by
  intro i hi
  have hB1 : 1 ≤ B := by rw [hBm]; exact Nat.one_le_two_pow
  have key := (τ_eq_zero_iff_digits g (q ^ 2 - 1 - b * l) mB hmB).1 hmask i
  rw [digit_pow_two hBm, digit_pow_two hBm, mask_digit hB1 hb hKL hl hq (by omega)] at key
  constructor
  · intro hi'
    rw [(ind_eq_zero_iff i).2 hi', mul_zero, Nat.sub_zero] at key
    have e : B - 1 = 2 ^ mB - 1 := by rw [hBm]
    rw [e] at key
    exact digit_zero_of_land_all_ones (by rw [← hBm]; exact Nat.mod_lt _ (by omega)) key
  · intro hi'
    rw [(ind_eq_one_iff i).2 hi', mul_one] at key
    exact key

/-- A number below `B^L` whose digits vanish off the support is the sum of its digits over
the support. -/
theorem g_eq_sum_supp {g : ℕ} (hB : 1 < B) (hKL : K m s ≤ L) (hg : g < B ^ L)
    (hdig : ∀ i < L, i ∉ supp m s → g / B ^ i % B = 0) :
    g = ∑ i ∈ supp m s, (g / B ^ i % B) * B ^ i := by
  conv_lhs => rw [← sum_digits hB L g hg]
  symm
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_range]
    have := mem_supp_lt hi; omega
  · intro i hi hi'
    rw [hdig i (Finset.mem_range.1 hi) hi', zero_mul]

/-- The digit polynomials evaluated at `B`. -/
theorem eval_Cmain_add_Cdum (x : ℤ) (z : Fin m → ℤ) (dum : Fin s → Fin 3 → ℤ) (B : ℤ) :
    (Cmain m x z + Cdum m s dum).eval B =
      x + ∑ i : Fin m, z i * B ^ (v i) + ∑ j : Fin s, ∑ e : Fin 3, dum j e * B ^ (t m s j + e) := by
  unfold Cmain Cdum
  simp [eval_finsetSum, eval_add, eval_mul, add_assoc]

/-- The coordinate digits of `g`. -/
def gdig (g B i : ℕ) : ℤ := ((g / B ^ i % B : ℕ) : ℤ)

/-- `x + g = C(B)` for the coordinates `zᵢ = digit_{vᵢ}(g)` and dummies `digit_{t_j+e}(g)`. -/
theorem C_eq_eval {g x : ℕ} (hB : 1 < B) (hKL : K m s ≤ L) (hg : g < B ^ L)
    (hdig : ∀ i < L, i ∉ supp m s → g / B ^ i % B = 0) :
    ((x + g : ℕ) : ℤ) = (Cmain m (x : ℤ) (fun i => gdig g B (v i)) +
      Cdum m s (fun j e => gdig g B (t m s j + e))).eval (B : ℤ) := by
  rw [eval_Cmain_add_Cdum]
  have hg' := g_eq_sum_supp hB hKL hg hdig
  rw [sum_supp (fun i => (g / B ^ i % B) * B ^ i)] at hg'
  unfold gdig
  have hcast : ((g : ℕ) : ℤ) = ∑ i : Fin m, ((g / B ^ (v i) % B : ℕ) : ℤ) * (B : ℤ) ^ (v i) +
      ∑ j : Fin s, ∑ e : Fin 3, ((g / B ^ (t m s j + e) % B : ℕ) : ℤ) * (B : ℤ) ^ (t m s j + e) := by
    conv_lhs => rw [hg']
    push_cast
    ring
  rw [Nat.cast_add, hcast]
  ring

/-- Reading the third mask: every digit of `σ` on the support is at most three. -/
theorem sigma_digits_le_three {mB σ θ : ℕ} (hmB : 2 ≤ mB) (hBm : B = 2 ^ mB) (hKL : K m s ≤ L)
    (hθ : θ = B - 4) (hl : l = ∑ h ∈ range L, ind m s h * B ^ h)
    (hmask : Jones1982.τ 2 σ (θ * l) = 0) :
    ∀ i ∈ supp m s, σ / B ^ i % B ≤ 3 := by
  intro i hi
  have hB4 : 4 ≤ B := by
    rw [hBm]; calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mB := Nat.pow_le_pow_right (by norm_num) hmB
  have hiL : i < 2 * L := by have := mem_supp_lt hi; omega
  have key := (τ_eq_zero_iff_digits σ (θ * l) mB (by omega)).1 hmask i
  rw [digit_pow_two hBm, digit_pow_two hBm, theta_mask_digit hB4 hKL hθ hl hiL,
    (ind_eq_one_iff i).2 hi, mul_one] at key
  have e : B - 4 = 2 ^ mB - 4 := by rw [hBm]
  rw [e] at key
  exact le_three_of_land hmB (by rw [← hBm]; exact Nat.mod_lt _ (by omega)) key

end Mask

end Iso

end Jones1980
