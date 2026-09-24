import Diophantine.Paper1980.Index90
import Diophantine.Paper1980.Mask93

/-!
# Reading the three masks of the 90-operation system digit by digit

`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, Section 4.  With `q = B^L`,
`B = 2^mB`, `b < B` and `l = ℓ₀(B) = Σ_{h<L} ind h · B^h`:

* the first mask `q² − 1 − b l` has base-`B` digit `B − 1` off the indicator
  support and `B − 1 − b = H₀` on it (`mask_digit`); the packed condition
  `g & (q² − 1 − b l) = 0` forces every digit of `g` off the support to vanish
  and every digit on the support to be disjoint from `H₀` (`g_digits`), so
  `x + g = C(B)` for the digit polynomial with the coordinates
  `zᵢ = digit_{vᵢ}(g)` and the dummies `digit_{r+e}(g)` (`C_eq_eval`);
* the middle mask `θ λ = (B − 2) Σ_{j<2L} B^j` makes the digits of `S₂` binary
  and, with the congruence `S₂ ≡ V (mod B − 2)`, identifies `S₂` with the
  radix-`B` value of the binary digit list of `V` (`S2_eq_ofDigits_two`);
* the third mask `θ l = (B − 2) ℓ₀(B)` has digit `B − 2` on the support and
  `0` off it, so `σ & θ l = 0` makes every digit of `σ` on the support binary
  (`sigma_digits_le_one`).
-/

namespace Jones1980

namespace L90

open Finset Polynomial Nat
open Layout (Row)
open Jones1982 (τ mask29)

noncomputable section

/-! ### Binary digit reading -/

/-- A digit disjoint from `2^m − 2` is at most one. -/
theorem le_one_of_land {x m : ℕ} (hm : 1 ≤ m) (hx : x < 2 ^ m) (h : x &&& (2 ^ m - 2) = 0) :
    x ≤ 1 := by
  have h1 : (x &&& (2 ^ m - 2)) >>> 1 = 0 := by rw [h]; rfl
  rw [Nat.shiftRight_and_distrib, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at h1
  have e : 2 ^ m = 2 ^ (m - 1) * 2 ^ 1 := by rw [← pow_add]; congr 1; omega
  have h2 : (2 ^ m - 2) / 2 ^ 1 = 2 ^ (m - 1) - 1 := by
    have e2 : 2 ^ m - 2 = (2 ^ (m - 1) - 1) * 2 := by
      rw [Nat.sub_mul, one_mul, ← pow_succ, Nat.sub_add_cancel hm]
    rw [e2, pow_one, Nat.mul_div_cancel _ (by norm_num)]
  rw [h2] at h1
  have h3 : x / 2 ^ 1 < 2 ^ (m - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [e] at hx; exact hx
  rw [Nat.and_two_pow_sub_one_of_lt_two_pow h3] at h1
  norm_num at h1
  omega

/-- `mask29 B 2 k = (B − 2) · geom B k`. -/
theorem mask29_two_eq_geom (B : ℕ) : ∀ k, mask29 B 2 k = (B - 2) * geom B k
  | 0 => by simp [Jones1982.mask29_zero, geom_zero]
  | k + 1 => by rw [Jones1982.mask29_succ, geom_succ, mask29_two_eq_geom B k]; ring

/-- `θλ = mask29 B 2 (2L)` for `θ = B − 2` and `λ (B − 1) = B^(2L) − 1`. -/
theorem theta_lam_eq_mask_two {B θ lam L : ℕ} (hB : 3 ≤ B) (hθ : θ + 2 = B)
    (hlam : lam * (B - 1) = B ^ (2 * L) - 1) : θ * lam = mask29 B 2 (2 * L) := by
  have hg := geom_mul_sub_one B (by omega) (2 * L)
  have : lam = geom B (2 * L) := by
    have h : lam * (B - 1) = geom B (2 * L) * (B - 1) := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  rw [this, mask29_two_eq_geom]
  congr 1; omega

/-- The canonical combined code: the middle mask and the binary congruence identify `S₂`
with the radix-`B` value of the binary digit list of `V`. -/
theorem S2_eq_ofDigits_two {B mB L S2 V θ lam t : ℕ} (hBm : B = 2 ^ mB) (ys : List ℕ)
    (hys : ∀ y ∈ ys, y < 2) (hlen : ys.length ≤ 2 * L) (hV : V = ofDigits 2 ys)
    (hθ : θ + 2 = B) (hlam : lam * (B - 1) = B ^ (2 * L) - 1)
    (hH : 2 * 2 ^ (2 * L + 1) ≤ B)
    (hS2 : S2 < B ^ (2 * L)) (hmask : τ 2 S2 (θ * lam) = 0) (hE45 : S2 = V + t * θ) :
    S2 = ofDigits B ys := by
  have hB3 : 3 ≤ B := by
    have : 2 * 2 ^ 1 ≤ 2 * 2 ^ (2 * L + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hm1 : 1 ≤ mB := by
    by_contra h; push Not at h
    interval_cases mB; simp_all
  have key := Jones1982.lemma_2_9 (s := 1) (t := mB) (n := 2 * L) (m := 2 * L) (k := 2 * L)
    le_rfl hm1 le_rfl le_rfl (by rw [← hBm, pow_one]; exact hH)
    (ys := ys) (fun y hy => by rw [pow_one]; exact hys y hy) (by omega) S2
  rw [← hBm] at key
  simp only [pow_one] at key
  apply key.2
  refine ⟨?_, ?_, ?_⟩
  · rw [← hV, hE45]
    show (V + t * θ) % (B - 2) = V % (B - 2)
    have : θ = B - 2 := by omega
    rw [this, Nat.add_mul_mod_self_right]
  · calc S2 < B ^ (2 * L) := hS2
      _ ≤ 2 * B ^ (2 * L) := Nat.le_mul_of_pos_left _ (by norm_num)
  · rw [← theta_lam_eq_mask_two hB3 hθ hlam]; exact hmask

/-! ### The masks of a layout -/

variable {m s : ℕ} (rows : Fin s → Row m) (hel : Fin s → Fin 3 → Fin m) (PX : Finset (Fin m))

/-- The sum over the indicator support splits into the coordinate weights and the tested
positions. -/
theorem sum_supp {M' : Type*} [AddCommMonoid M'] (f : ℕ → M') :
    ∑ i ∈ supp rows, f i =
      ∑ i : Fin m, f (v i) + ∑ r ∈ Rset s rows, ∑ e : Fin 3, f (r + e) := by
  unfold supp
  have hdisj : Disjoint (Finset.univ.image fun i : Fin m => v (i : ℕ))
      ((Rset s rows).biUnion fun r => {r, r + 1, r + 2}) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_image] at ha
    obtain ⟨i, _, rfl⟩ := ha
    rw [Finset.mem_biUnion] at hb
    obtain ⟨r, hr, hr'⟩ := hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr'
    have := v_le_M i.isLt
    have := (Rset_bounds rows hr).1
    have := t_zero_ge m s
    omega
  rw [Finset.sum_union hdisj, Finset.sum_image (fun i _ k _ h => Fin.ext (v_inj h)),
    Finset.sum_biUnion]
  · congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton,
      Fin.sum_univ_three]
    simp [add_assoc]
  · intro r hr r' hr' hrr
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    obtain ⟨j, hj⟩ := (mem_Rset s rows).1 hr
    obtain ⟨j', hj'⟩ := (mem_Rset s rows).1 hr'
    have := eight_dvd_of_mem_starts rows hj
    have := eight_dvd_of_mem_starts rows hj'
    omega

variable {B L b q l : ℕ}

/-- `ℓ₀(B)` extended to `2L` digits. -/
theorem ell0_sum_extend (hKL : K m s ≤ L) :
    ∑ h ∈ range L, ind rows h * B ^ h = ∑ h ∈ range (2 * L), ind rows h * B ^ h := by
  apply Finset.sum_subset (Finset.range_mono (show L ≤ 2 * L by omega))
  intro h _ hh
  rw [Finset.mem_range] at hh
  rw [ind_eq_zero_of_ge rows (show K m s ≤ h by omega), zero_mul]

/-- The first mask as a digit sum. -/
theorem mask_eq (hB : 1 ≤ B) (hb : b < B) (hKL : K m s ≤ L)
    (hl : l = ∑ h ∈ range L, ind rows h * B ^ h) (hq : q = B ^ L) :
    q ^ 2 - 1 - b * l = ∑ i ∈ range (2 * L), (B - 1 - b * ind rows i) * B ^ i := by
  have h1 : q ^ 2 - 1 = ∑ i ∈ range (2 * L), (B - 1) * B ^ i := by
    have := Iso.sum_pred_mul_pow hB (2 * L)
    rw [hq, ← pow_mul, mul_comm L 2]; omega
  have h2 : b * l = ∑ i ∈ range (2 * L), b * ind rows i * B ^ i := by
    rw [hl, ell0_sum_extend rows hKL, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h1, h2, ← Finset.sum_tsub_distrib]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Nat.sub_mul (B - 1) (b * ind rows i) (B ^ i)]
  · intro i _
    have := ind_le_one rows i
    have : b * ind rows i ≤ B - 1 := by
      calc b * ind rows i ≤ b * 1 := Nat.mul_le_mul_left _ this
        _ ≤ B - 1 := by omega
    exact Nat.mul_le_mul_right _ this

/-- The digit of the first mask at `i < 2L` is `B − 1 − b · ind i`. -/
theorem mask_digit (hB : 1 ≤ B) (hb : b < B) (hKL : K m s ≤ L)
    (hl : l = ∑ h ∈ range L, ind rows h * B ^ h) (hq : q = B ^ L) {i : ℕ} (hi : i < 2 * L) :
    (q ^ 2 - 1 - b * l) / B ^ i % B = B - 1 - b * ind rows i := by
  rw [mask_eq rows hB hb hKL hl hq, Iso.digit_sum (by omega) i _ (fun i => by omega), if_pos hi]

/-- The third mask `θ l` as a digit sum. -/
theorem theta_mask_digit (hB : 2 ≤ B) (hKL : K m s ≤ L) {θ : ℕ} (hθ : θ = B - 2)
    (hl : l = ∑ h ∈ range L, ind rows h * B ^ h) {i : ℕ} (hi : i < 2 * L) :
    θ * l / B ^ i % B = (B - 2) * ind rows i := by
  have h : θ * l = ∑ i ∈ range (2 * L), (B - 2) * ind rows i * B ^ i := by
    rw [hl, ell0_sum_extend rows hKL, Finset.mul_sum, hθ]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h, Iso.digit_sum (by omega) i _ (fun i => by
    have := ind_le_one rows i
    calc (B - 2) * ind rows i ≤ (B - 2) * 1 := Nat.mul_le_mul_left _ this
      _ < B := by omega), if_pos hi]

/-- Reading the first mask: off the support the digits of `g` vanish, on the support they
are disjoint from `B − 1 − b`. -/
theorem g_digits {mB g : ℕ} (hmB : 0 < mB) (hBm : B = 2 ^ mB) (hb : b < B) (hKL : K m s ≤ L)
    (hl : l = ∑ h ∈ range L, ind rows h * B ^ h) (hq : q = B ^ L)
    (hmask : τ 2 g (q ^ 2 - 1 - b * l) = 0) :
    ∀ i < L, (i ∉ supp rows → g / B ^ i % B = 0) ∧
      (i ∈ supp rows → (g / B ^ i % B) &&& (B - 1 - b) = 0) := by
  intro i hi
  have hB1 : 1 ≤ B := by rw [hBm]; exact Nat.one_le_two_pow
  have key := (τ_eq_zero_iff_digits g (q ^ 2 - 1 - b * l) mB hmB).1 hmask i
  rw [Iso.digit_pow_two hBm, Iso.digit_pow_two hBm, mask_digit rows hB1 hb hKL hl hq (by omega)]
    at key
  constructor
  · intro hi'
    rw [(ind_eq_zero_iff rows i).2 hi', mul_zero, Nat.sub_zero] at key
    have e : B - 1 = 2 ^ mB - 1 := by rw [hBm]
    rw [e] at key
    exact digit_zero_of_land_all_ones (by rw [← hBm]; exact Nat.mod_lt _ (by omega)) key
  · intro hi'
    rw [(ind_eq_one_iff rows i).2 hi', mul_one] at key
    exact key

/-- A number below `B^L` whose digits vanish off the support is the sum of its digits over
the support. -/
theorem g_eq_sum_supp {g : ℕ} (hB : 1 < B) (hKL : K m s ≤ L) (hg : g < B ^ L)
    (hdig : ∀ i < L, i ∉ supp rows → g / B ^ i % B = 0) :
    g = ∑ i ∈ supp rows, (g / B ^ i % B) * B ^ i := by
  conv_lhs => rw [← Iso.sum_digits hB L g hg]
  symm
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_range]
    have := mem_supp_lt rows hi; omega
  · intro i hi hi'
    rw [hdig i (Finset.mem_range.1 hi) hi', zero_mul]

/-- The digit polynomials evaluated at `B`. -/
theorem eval_Cmain_add_Cdum (x : ℤ) (z : Fin m → ℤ) (dum : ℕ → Fin 3 → ℤ) (B : ℤ) :
    (Cmain x z + Cdum s rows dum).eval B =
      x + ∑ i : Fin m, z i * B ^ (v i) + ∑ r ∈ Rset s rows, ∑ e : Fin 3, dum r e * B ^ (r + e) := by
  unfold Cmain Cdum
  simp [eval_finsetSum, eval_add, eval_mul, add_assoc]

/-- The coordinate digits of `g`. -/
def gdig (g B i : ℕ) : ℤ := ((g / B ^ i % B : ℕ) : ℤ)

/-- `x + g = C(B)` for the coordinates `zᵢ = digit_{vᵢ}(g)` and dummies `digit_{r+e}(g)`. -/
theorem C_eq_eval {g x : ℕ} (hB : 1 < B) (hKL : K m s ≤ L) (hg : g < B ^ L)
    (hdig : ∀ i < L, i ∉ supp rows → g / B ^ i % B = 0) :
    ((x + g : ℕ) : ℤ) = (Cmain (x : ℤ) (fun i : Fin m => gdig g B (v i)) +
      Cdum s rows (fun r e => gdig g B (r + e))).eval (B : ℤ) := by
  rw [eval_Cmain_add_Cdum]
  have hg' := g_eq_sum_supp rows hB hKL hg hdig
  rw [sum_supp rows (fun i => (g / B ^ i % B) * B ^ i)] at hg'
  unfold gdig
  have hcast : ((g : ℕ) : ℤ) = ∑ i : Fin m, ((g / B ^ (v i) % B : ℕ) : ℤ) * (B : ℤ) ^ (v i) +
      ∑ r ∈ Rset s rows, ∑ e : Fin 3, ((g / B ^ (r + e) % B : ℕ) : ℤ) * (B : ℤ) ^ (r + e) := by
    conv_lhs => rw [hg']
    push_cast
    ring
  rw [Nat.cast_add, hcast]
  ring

/-- Reading the third mask: every digit of `σ` on the support is binary. -/
theorem sigma_digits_le_one {mB σ θ : ℕ} (hmB : 1 ≤ mB) (hBm : B = 2 ^ mB) (hKL : K m s ≤ L)
    (hθ : θ = B - 2) (hl : l = ∑ h ∈ range L, ind rows h * B ^ h)
    (hmask : τ 2 σ (θ * l) = 0) :
    ∀ i ∈ supp rows, σ / B ^ i % B ≤ 1 := by
  intro i hi
  have hB2 : 2 ≤ B := by
    rw [hBm]; calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ mB := Nat.pow_le_pow_right (by norm_num) hmB
  have hiL : i < 2 * L := by have := mem_supp_lt rows hi; omega
  have key := (τ_eq_zero_iff_digits σ (θ * l) mB (by omega)).1 hmask i
  rw [Iso.digit_pow_two hBm, Iso.digit_pow_two hBm, theta_mask_digit rows hB2 hKL hθ hl hiL,
    (ind_eq_one_iff rows i).2 hi, mul_one] at key
  have e : B - 2 = 2 ^ mB - 2 := by rw [hBm]
  rw [e] at key
  exact le_one_of_land hmB (by rw [← hBm]; exact Nat.mod_lt _ (by omega)) key

end

end L90

end Jones1980
