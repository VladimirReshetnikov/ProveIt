import Diophantine.Paper1980.Sigma90
import Diophantine.Paper1980.Window90

/-!
# The windows of the tested starts (Section 5 of `BINARY_PRODUCT_90_PROOF.md`)

For a valid layout, a start `r` of band `j`, and `σ = Σ_{p<K} a_p B^p + B^K High`
with `a_p = [X^p](D · (C_main + C_dum)²)`: the positions `r − 6, r − 5` are
empty, `r − 4` carries the reset value `≥ x²`, `r − 3, r − 2` are empty, `r − 1`
carries the (nonnegative) padding value `y`, and the three digits of `σ` at
`r, r + 1, r + 2` show `a_r + ⌊y / B⌋` modulo `B³`, a value that is small
(`window_residue`).  With binary digits the window value is read off exactly
(`window_value`).
-/

namespace Jones1980

namespace L90

open Polynomial Finset
open Layout (Row)
open Iso (absSum absSum_nonneg tail_le sum_range_split)

noncomputable section

variable {m s : ℕ} (rows : Fin s → Row m) (hel : Fin s → Fin 3 → Fin m) (PX : Finset (Fin m))

/-- The raw coefficient at `p`. -/
def a (x : ℤ) (z : Fin m → ℤ) (p : ℕ) : ℤ := (D s rows hel PX * Cmain x z ^ 2).coeff p

set_option maxHeartbeats 2000000 in
/-- The residue of the window of a start `r`: the three digits at `r, r + 1, r + 2` show
`a_r + ⌊a_{r−1} / B⌋` modulo `B³`, and that value is small. -/
theorem window_residue (hL : LayoutOk s rows hel) {B x σ : ℕ} (hB : 64 ≤ B) (hx : 1 ≤ x)
    (hxB : x < B) (z : Fin m → ℤ) (hz0 : ∀ i, 0 ≤ z i) (hzB : ∀ i, z i ≤ B)
    (dum : ℕ → Fin 3 → ℤ)
    (hD1 : 128 * absSum (D s rows hel PX) * ((m : ℤ) + 1) ^ 2 < B)
    (High : ℤ)
    (hσ : (σ : ℤ) = ∑ p ∈ range (K m s),
      (D s rows hel PX * (Cmain x z + Cdum s rows dum) ^ 2).coeff p * (B : ℤ) ^ p +
      (B : ℤ) ^ (K m s) * High)
    (j : Fin s) {r : ℕ} (hr : r ∈ starts s rows j) :
    ((σ / B ^ r : ℕ) : ℤ) % (B : ℤ) ^ 3 =
      (a rows hel PX x z r + a rows hel PX x z (r - 1) / B) % (B : ℤ) ^ 3 ∧
    64 * |a rows hel PX x z r + a rows hel PX x z (r - 1) / B| < (B : ℤ) ^ 3 ∧
    0 ≤ a rows hel PX x z (r - 1) := by
  set Dp := D s rows hel PX with hDp
  set a' : ℕ → ℤ := fun p => (Dp * (Cmain x z + Cdum s rows dum) ^ 2).coeff p with ha'
  have hM := M_pos m
  have hs := hL.three_le
  have htj := t_ge m s j
  obtain ⟨hb1, hb2⟩ := starts_bounds rows hr
  have h8 := eight_dvd_of_mem_starts rows hr
  have hrtl : r ≤ tl m s := le_trans hb2 (t_le_tl j)
  obtain ⟨u, hu⟩ : ∃ u, r = u + 6 := ⟨r - 6, by omega⟩
  have hu1 : 1 ≤ u := by omega
  have htK : u + 9 ≤ K m s := by unfold K; omega
  have hBZ : (64 : ℤ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℤ) < B := by linarith
  have hxZ : (x : ℤ) ≤ B - 1 := by
    have : (x : ℤ) < B := by exact_mod_cast hxB
    linarith
  have hx1 : (1 : ℤ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℤ) ≤ x := by linarith
  -- the coefficients up to `t_last + 2` are those of `D · C_main²`
  have hamain : ∀ p, p ≤ tl m s + 2 → a' p = a rows hel PX x z p :=
    fun p hp => coeff_eq_main rows hel PX x z (by omega) dum p hp
  -- the coefficient bound
  set KB : ℤ := absSum Dp * (((m : ℤ) + 1) * B) ^ 2 with hKB
  have hD1' : 0 ≤ absSum Dp := absSum_nonneg _
  have hKB0 : 0 ≤ KB := by positivity
  have hsum : ∑ i, z i ≤ (m : ℤ) * B := by
    calc ∑ i : Fin m, z i ≤ ∑ i : Fin m, (B : ℤ) := Finset.sum_le_sum fun i _ => hzB i
      _ = (m : ℤ) * B := by simp
  have hsum0 : 0 ≤ ∑ i, z i := Finset.sum_nonneg fun i _ => hz0 i
  have hbound : ∀ p, p ≤ tl m s + 2 → |a' p| ≤ KB := by
    intro p hp
    rw [hamain p hp]
    refine le_trans (abs_coeff_le rows hel PX x z hx0 hz0 p) ?_
    apply mul_le_mul_of_nonneg_left _ hD1'
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hsum, hxZ, hBZ]
  -- the nine positions of the window
  have hempty : ∀ k, k < 9 → k ≠ 2 → k ≠ 5 → k ≠ 6 → a' (u + k) = 0 := by
    intro k hk h2 h5 h6
    rw [hamain _ (by omega)]
    apply coeff_at_empty rows hel PX x z hL j hr (u + k) (by omega) (by omega) (by omega)
      (by omega)
    intro hk' hj
    -- `p = r − 1` with `j` the last row: then `r = t_last` and the position is the padding
    -- position, excluded by `k ≠ 5`
    omega
  have hreset : (x : ℤ) ^ 2 ≤ a' (u + 2) := by
    rw [hamain _ (by omega), show u + 2 = r - 4 by omega]
    exact coeff_at_reset rows hel PX x z hL hx0 hz0 j hr
  have hpad0 : 0 ≤ a' (u + 5) := by
    rw [hamain _ (by omega), show u + 5 = r - 1 by omega]
    unfold a
    by_cases hlast : (j : ℕ) = s - 1
    · have hstart : r = tl m s := by
        have hneg := (hL.last j hlast).1
        rcases (mem_starts s rows).1 hr with h | ⟨μ, hμ, _⟩
        · rw [h]; unfold tl; rw [← hlast]
        · rw [hneg] at hμ; simp at hμ
      rw [hstart, coeff_at_pad rows hel PX x z hL]
      exact Finset.sum_nonneg fun h _ => mul_nonneg (mul_nonneg (by norm_num) hx0) (hz0 h)
    · rw [coeff_at_empty rows hel PX x z hL j hr (r - 1) (by omega) (by omega) (by omega)
        (by omega) (fun _ => hlast)]
  have hpadeq : a' (u + 5) = a rows hel PX x z (r - 1) := by
    rw [hamain _ (by omega), show u + 5 = r - 1 by omega]
  have hGeq : a' (u + 6) = a rows hel PX x z r := by
    rw [hamain _ (by omega), show u + 6 = r by omega]
  -- the decomposition of `σ` around the window
  have hsplit := sum_range_split a' (B : ℤ) (K := u + 9) (N := K m s) htK
  rw [hsplit, Finset.sum_range_add] at hσ
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at hσ
  have e0 : a' u = 0 := by
    simpa using hempty 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [e0, hempty 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hempty 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hempty 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hempty 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hempty 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at hσ
  set Low : ℤ := ∑ p ∈ range u, a' p * (B : ℤ) ^ p with hLow
  set High' : ℤ := (∑ p ∈ range (K m s - (u + 9)), a' (u + 9 + p) * (B : ℤ) ^ p) +
    (B : ℤ) ^ (K m s - (u + 9)) * High with hHigh'
  have hσ' : (σ : ℤ) = Low + a' (u + 2) * (B : ℤ) ^ (u + 6 - 4) +
      a' (u + 5) * (B : ℤ) ^ (u + 6 - 1) + a' (u + 6) * (B : ℤ) ^ (u + 6) +
      (B : ℤ) ^ (u + 6 + 3) * High' := by
    rw [hσ, hHigh', show u + 6 - 4 = u + 2 by omega, show u + 6 - 1 = u + 5 by omega,
      show u + 6 + 3 = u + 9 by omega,
      show (B : ℤ) ^ (K m s) = B ^ (u + 9) * B ^ (K m s - (u + 9)) by
        rw [← pow_add]; congr 1; omega]
    simp only [zero_mul, add_zero, zero_add]
    ring
  -- the low part is small
  have hLowB : 32 * |Low| ≤ (B : ℤ) ^ (u + 6 - 4) := by
    set a'' : ℕ → ℤ := fun p => if p ≤ tl m s + 2 then a' p else 0 with ha''
    have hLow' : Low = ∑ p ∈ range u, a'' p * (B : ℤ) ^ p := by
      rw [hLow]; apply Finset.sum_congr rfl; intro p hp
      rw [Finset.mem_range] at hp
      simp only [ha'']; rw [if_pos (by omega)]
    have ha''b : ∀ p, |a'' p| ≤ KB := fun p => by
      simp only [ha'']; split_ifs with hp
      · exact hbound p hp
      · simpa using hKB0
    have htail := tail_le (B := B) (N := u) (by omega) hu1 ha''b
    rw [← hLow'] at htail
    have e : (B : ℤ) ^ (u + 6 - 4) = B ^ 3 * B ^ (u - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    have hKB3 : 64 * KB ≤ (B : ℤ) ^ 3 := by
      have h1 : 128 * absSum Dp * ((m : ℤ) + 1) ^ 2 * B ^ 2 ≤ B * B ^ 2 :=
        mul_le_mul_of_nonneg_right hD1.le (by positivity)
      have hX : 0 ≤ absSum Dp * ((m : ℤ) + 1) ^ 2 * B ^ 2 := by positivity
      calc 64 * KB = 64 * (absSum Dp * ((m : ℤ) + 1) ^ 2 * B ^ 2) := by rw [hKB]; ring
        _ ≤ 128 * (absSum Dp * ((m : ℤ) + 1) ^ 2 * B ^ 2) := by linarith only [hX]
        _ = 128 * absSum Dp * ((m : ℤ) + 1) ^ 2 * B ^ 2 := by ring
        _ ≤ B * B ^ 2 := h1
        _ = (B : ℤ) ^ 3 := by ring
    have hp : (0 : ℤ) ≤ B ^ (u - 1) := by positivity
    calc 32 * |Low| ≤ 32 * (KB * (2 * (B : ℤ) ^ (u - 1))) :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = 64 * KB * B ^ (u - 1) := by ring
      _ ≤ B ^ 3 * B ^ (u - 1) := mul_le_mul_of_nonneg_right hKB3 hp
  -- the reset value is at least one and below `B³`
  have hx2a : 1 ≤ a' (u + 2) := le_trans (one_le_pow₀ hx1) hreset
  have hKB3' : 128 * KB < (B : ℤ) ^ 3 := by
    have h1 : 128 * absSum Dp * ((m : ℤ) + 1) ^ 2 * B ^ 2 < B * B ^ 2 :=
      mul_lt_mul_of_pos_right hD1 (by positivity)
    calc 128 * KB = 128 * absSum Dp * ((m : ℤ) + 1) ^ 2 * B ^ 2 := by rw [hKB]; ring
      _ < B * B ^ 2 := h1
      _ = (B : ℤ) ^ 3 := by ring
  have hx2b : a' (u + 2) + 1 ≤ (B : ℤ) ^ 3 := by
    have := le_trans (le_abs_self _) (hbound (u + 2) (by omega))
    linarith
  -- the window
  have hwin := window_digits_pad90 hB (by omega) hσ' hLowB hx2a hx2b hpad0
  rw [hpadeq, hGeq] at hwin
  rw [← hu] at hwin
  -- the value is small
  have hG : 64 * |a rows hel PX x z r + a rows hel PX x z (r - 1) / B| < (B : ℤ) ^ 3 := by
    have hG1 : |a rows hel PX x z r| ≤ KB := by rw [← hGeq]; exact hbound _ (by omega)
    have hP1 : a rows hel PX x z (r - 1) ≤ KB := by
      rw [← hpadeq]; exact le_trans (le_abs_self _) (hbound _ (by omega))
    have hP0 : 0 ≤ a rows hel PX x z (r - 1) := hpadeq ▸ hpad0
    have hP2 : a rows hel PX x z (r - 1) / B ≤ a rows hel PX x z (r - 1) := Int.ediv_le_self _ hP0
    have hP3 : 0 ≤ a rows hel PX x z (r - 1) / B := Int.ediv_nonneg hP0 hB0.le
    have habs : |a rows hel PX x z r + a rows hel PX x z (r - 1) / B| ≤ 2 * KB := by
      calc |a rows hel PX x z r + a rows hel PX x z (r - 1) / B|
          ≤ |a rows hel PX x z r| + |a rows hel PX x z (r - 1) / B| := abs_add_le _ _
        _ = |a rows hel PX x z r| + a rows hel PX x z (r - 1) / B := by rw [abs_of_nonneg hP3]
        _ ≤ KB + KB := by linarith only [hG1, hP1, hP2]
        _ = 2 * KB := by ring
    calc 64 * |a rows hel PX x z r + a rows hel PX x z (r - 1) / B| ≤ 64 * (2 * KB) :=
          mul_le_mul_of_nonneg_left habs (by norm_num)
      _ = 128 * KB := by ring
      _ < (B : ℤ) ^ 3 := hKB3'
  exact ⟨hwin, hG, hpadeq ▸ hpad0⟩

/-- The value of a window with binary digits: `a_r + ⌊a_{r−1} / B⌋ ≥ 0` and it is the
three-digit number read at `r, r + 1, r + 2`. -/
theorem window_value (hL : LayoutOk s rows hel) {B x σ : ℕ} (hB : 64 ≤ B) (hx : 1 ≤ x)
    (hxB : x < B) (z : Fin m → ℤ) (hz0 : ∀ i, 0 ≤ z i) (hzB : ∀ i, z i ≤ B)
    (dum : ℕ → Fin 3 → ℤ)
    (hD1 : 128 * absSum (D s rows hel PX) * ((m : ℤ) + 1) ^ 2 < B)
    (High : ℤ)
    (hσ : (σ : ℤ) = ∑ p ∈ range (K m s),
      (D s rows hel PX * (Cmain x z + Cdum s rows dum) ^ 2).coeff p * (B : ℤ) ^ p +
      (B : ℤ) ^ (K m s) * High)
    (j : Fin s) {r : ℕ} (hr : r ∈ starts s rows j)
    (hd0 : σ / B ^ r % B ≤ 1) (hd1 : σ / B ^ (r + 1) % B ≤ 1) (hd2 : σ / B ^ (r + 2) % B ≤ 1) :
    0 ≤ a rows hel PX x z r + a rows hel PX x z (r - 1) / B ∧
    a rows hel PX x z r + a rows hel PX x z (r - 1) / B =
      ((σ / B ^ r % B : ℕ) : ℤ) + ((σ / B ^ (r + 1) % B : ℕ) : ℤ) * B +
        ((σ / B ^ (r + 2) % B : ℕ) : ℤ) * B ^ 2 := by
  obtain ⟨hwin, hG, _⟩ :=
    window_residue rows hel PX hL hB hx hxB z hz0 hzB dum hD1 High hσ j hr
  exact window_value_bin hB hG hwin hd0 hd1 hd2

end

end L90

end Jones1980
