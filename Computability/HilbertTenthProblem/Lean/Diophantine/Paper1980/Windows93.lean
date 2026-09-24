import Diophantine.Paper1980.Sigma93
import Diophantine.Paper1980.Window93b

/-!
# The window of every target (Section 5)

Combining the decomposition `σ = Σ_{p<K} a_p B^p + B^K High`, the isolation
values `a_{t−3} = x²`, `a_{t−1} = pad_j`, `a_t = G_j`, the vanishing of the
five other positions of the window, the coefficient bound `|a_p| ≤ D₁ (x + Σ zᵢ)²`
and the third mask: for every target `j`, the value `G_j + ⌊pad_j / B⌋` is
nonnegative and equals the three-digit number read at `t_j, t_j + 1, t_j + 2`
(`window_value`).  Here `pad_j = 0` except for the two padded unit targets,
where it is `x² + 2x Σ_{q ∈ P} z_q`.
-/

namespace Jones1980

namespace Iso

open Polynomial Layout Finset

noncomputable section

/-- The three digits of a window as casts of natural digits. -/
theorem window_digits_cast (B t σ : ℕ) :
    (((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3) % B = ((σ / B ^ t % B : ℕ) : ℤ) ∧
    (((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3) / B % B = ((σ / B ^ (t + 1) % B : ℕ) : ℤ) ∧
    (((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3) / B / B = ((σ / B ^ (t + 2) % B : ℕ) : ℤ) := by
  have hN : ((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3 = ((σ / B ^ t % B ^ 3 : ℕ) : ℤ) := by norm_cast
  rw [hN]
  have e1 : σ / B ^ t / B = σ / B ^ (t + 1) := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have e2 : σ / B ^ t / B ^ 2 = σ / B ^ (t + 2) := by rw [pow_add, Nat.div_div_eq_div_mul]
  refine ⟨?_, ?_, ?_⟩
  · have : (σ / B ^ t % B ^ 3 % B : ℕ) = σ / B ^ t % B :=
      Nat.mod_mod_of_dvd _ (dvd_pow_self B (by norm_num))
    exact_mod_cast this
  · have : (σ / B ^ t % B ^ 3 / B % B : ℕ) = σ / B ^ (t + 1) % B := by
      have := digit_mod_pow (σ / B ^ t) B (show 1 < 3 by norm_num)
      rw [pow_one] at this
      rw [this, e1]
    exact_mod_cast this
  · have : (σ / B ^ t % B ^ 3 / B / B : ℕ) = σ / B ^ (t + 2) % B := by
      rw [digit_mod_pow_three_top, e2]
    exact_mod_cast this

section Windows

variable {m s : ℕ} (rows : Fin s → Row m) (P5 P7 : Finset (Fin m))

/-- The padding coefficient of target `j`. -/
def padVal (x : ℤ) (z : Fin m → ℤ) (j : Fin s) : ℤ :=
  (if (j : ℕ) = s - 2 then x ^ 2 + ∑ q ∈ P5, 2 * x * z q else 0) +
  (if (j : ℕ) = s - 1 then x ^ 2 + ∑ q ∈ P7, 2 * x * z q else 0)

theorem padVal_nonneg (x : ℤ) (hx : 0 ≤ x) (z : Fin m → ℤ) (hz : ∀ i, 0 ≤ z i) (j : Fin s) :
    0 ≤ padVal P5 P7 x z j := by
  unfold padVal
  have : ∀ P : Finset (Fin m), 0 ≤ x ^ 2 + ∑ q ∈ P, 2 * x * z q := fun P =>
    add_nonneg (sq_nonneg x) (Finset.sum_nonneg fun q _ =>
      mul_nonneg (mul_nonneg (by norm_num) hx) (hz q))
  refine add_nonneg ?_ ?_ <;> split_ifs <;> first | exact this _ | exact le_rfl

theorem padVal_of_lt (x : ℤ) (z : Fin m → ℤ) (j : Fin s) (hj : (j : ℕ) + 2 < s) :
    padVal P5 P7 x z j = 0 := by
  unfold padVal
  rw [if_neg (by omega), if_neg (by omega)]; rfl

set_option maxHeartbeats 2000000 in
/-- The residue of the window of target `j`: the three digits at `t_j, t_j + 1, t_j + 2` show
`G_j + ⌊pad_j / B⌋` modulo `B³`, and that value is small. -/
theorem window_residue (hs : 3 ≤ s) {B x σ : ℕ} (hB : 64 ≤ B) (hx : 1 ≤ x) (hxB : x < B)
    (z : Fin m → ℤ) (hz0 : ∀ i, 0 ≤ z i) (hzB : ∀ i, z i ≤ B) (dum : Fin s → Fin 3 → ℤ)
    (hD1 : 128 * absSum (D m s rows P5 P7) * ((m : ℤ) + 1) ^ 2 < B)
    (High : ℤ)
    (hσ : (σ : ℤ) = ∑ p ∈ range (K m s),
      (D m s rows P5 P7 * (Cmain m x z + Cdum m s dum) ^ 2).coeff p * (B : ℤ) ^ p +
      (B : ℤ) ^ (K m s) * High)
    (j : Fin s) (hcross : ∀ q ∈ (rows j).cross, q.1 ≠ q.2.1) :
    ((σ / B ^ (t m s j) : ℕ) : ℤ) % (B : ℤ) ^ 3 =
      ((rows j).val x z + padVal P5 P7 x z j / B) % (B : ℤ) ^ 3 ∧
    64 * |(rows j).val x z + padVal P5 P7 x z j / B| < (B : ℤ) ^ 3 := by
  set Dp := D m s rows P5 P7 with hDp
  set a : ℕ → ℤ := fun p => (Dp * (Cmain m x z + Cdum m s dum) ^ 2).coeff p with ha
  have hM := M_pos m
  have ht := t_ge_two_M m s j
  obtain ⟨u, hu⟩ : ∃ u, t m s j = u + 5 := ⟨t m s j - 5, by omega⟩
  have hu1 : 1 ≤ u := by omega
  have hlast : t m s j ≤ t m s (s - 1) := t_mono (by omega)
  have htK : u + 8 ≤ K m s := by unfold K; omega
  have hBZ : (64 : ℤ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℤ) < B := by linarith
  have hxZ : (x : ℤ) ≤ B - 1 := by
    have : (x : ℤ) < B := by exact_mod_cast hxB
    linarith
  have hx1 : (1 : ℤ) ≤ x := by exact_mod_cast hx
  have h6 := six_dvd_t m s j
  -- the coefficients below `t_{s−1} + 2` are those of `D · C_main²`
  have hamain : ∀ p, p ≤ t m s (s - 1) + 2 → a p = (Dp * Cmain m x z ^ 2).coeff p :=
    fun p hp => coeff_eq_main rows P5 P7 x z dum (by omega) p hp
  -- the coefficient bound
  set KB : ℤ := absSum Dp * (((m : ℤ) + 1) * B) ^ 2 with hKB
  have hD1' : 0 ≤ absSum Dp := absSum_nonneg _
  have hKB0 : 0 ≤ KB := by positivity
  have hsum : ∑ i, z i ≤ (m : ℤ) * B := by
    calc ∑ i : Fin m, z i ≤ ∑ i : Fin m, (B : ℤ) := Finset.sum_le_sum fun i _ => hzB i
      _ = (m : ℤ) * B := by simp
  have hsum0 : 0 ≤ ∑ i, z i := Finset.sum_nonneg fun i _ => hz0 i
  have hbound : ∀ p, p ≤ t m s (s - 1) + 2 → |a p| ≤ KB := by
    intro p hp
    rw [hamain p hp]
    refine le_trans (abs_coeff_le rows P5 P7 x z (by positivity) hz0 p) ?_
    apply mul_le_mul_of_nonneg_left _ hD1'
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hsum, hxZ, hBZ]
  -- the eight positions of the window
  have hval : a u = 0 ∧ a (u + 1) = 0 ∧ a (u + 2) = (x : ℤ) ^ 2 ∧ a (u + 3) = 0 ∧
      a (u + 4) = padVal P5 P7 x z j ∧ a (u + 5) = (rows j).val x z ∧ a (u + 6) = 0 ∧
      a (u + 7) = 0 := by
    have hempty : ∀ k, k < 8 → k ≠ 2 → k ≠ 4 → k ≠ 5 → a (u + k) = 0 := by
      intro k hk h2 h4 h5
      rw [hamain _ (by omega)]
      apply coeff_at_empty rows P5 P7 x z hs j (u + k) (by omega) (by omega)
      · omega
      · omega
      · omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hempty 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact hempty 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · rw [hamain _ (by omega), show u + 2 = t m s j - 3 by omega]
      exact coeff_at_reset rows P5 P7 x z hs j
    · exact hempty 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · rw [hamain _ (by omega), show u + 4 = t m s j - 1 by omega]
      exact coeff_at_pad rows P5 P7 x z hs j
    · rw [hamain _ (by omega), ← hu]
      exact coeff_at_target rows P5 P7 x z hs j hcross
    · exact hempty 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact hempty 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨h0, h1, h2, h3, h4, h5, h6', h7⟩ := hval
  -- the decomposition of `σ` around the window
  have hsplit := sum_range_split a (B : ℤ) (K := u + 8) (N := K m s) htK
  rw [hsplit, Finset.sum_range_add] at hσ
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at hσ
  rw [h0, h1, h2, h3, h4, h5, h6', h7] at hσ
  set Low : ℤ := ∑ p ∈ range u, a p * (B : ℤ) ^ p with hLow
  set High' : ℤ := (∑ p ∈ range (K m s - (u + 8)), a (u + 8 + p) * (B : ℤ) ^ p) +
    (B : ℤ) ^ (K m s - (u + 8)) * High with hHigh'
  have hσ' : (σ : ℤ) = Low + (x : ℤ) ^ 2 * (B : ℤ) ^ (u + 5 - 3) +
      padVal P5 P7 x z j * (B : ℤ) ^ (u + 5 - 1) + (rows j).val x z * (B : ℤ) ^ (u + 5) +
      (B : ℤ) ^ (u + 5 + 3) * High' := by
    rw [hσ, hHigh', show u + 5 - 3 = u + 2 by omega, show u + 5 - 1 = u + 4 by omega,
      show u + 5 + 3 = u + 8 by omega,
      show (B : ℤ) ^ (K m s) = B ^ (u + 8) * B ^ (K m s - (u + 8)) by
        rw [← pow_add]; congr 1; omega]
    ring
  -- the low part is small
  have hLowB : 32 * |Low| ≤ (B : ℤ) ^ (u + 5 - 3) := by
    set a' : ℕ → ℤ := fun p => if p ≤ t m s (s - 1) + 2 then a p else 0 with ha'
    have hLow' : Low = ∑ p ∈ range u, a' p * (B : ℤ) ^ p := by
      rw [hLow]; apply Finset.sum_congr rfl; intro p hp
      rw [Finset.mem_range] at hp
      simp only [ha']; rw [if_pos (by omega)]
    have ha'b : ∀ p, |a' p| ≤ KB := fun p => by
      simp only [ha']; split_ifs with hp
      · exact hbound p hp
      · simpa using hKB0
    have htail := tail_le (B := B) (N := u) (by omega) hu1 ha'b
    rw [← hLow'] at htail
    have e : (B : ℤ) ^ (u + 5 - 3) = B ^ 3 * B ^ (u - 1) := by
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
  -- the window
  have hpad0 := padVal_nonneg P5 P7 (x : ℤ) (by positivity) z hz0 j
  have hx2 : (x : ℤ) ^ 2 + 1 ≤ (B : ℤ) ^ 2 := by
    have := mul_le_mul hxZ hxZ (by linarith only [hx1]) (by linarith only [hBZ])
    nlinarith only [this, hBZ]
  have hwin := window_digits_pad hB (by omega) hσ' hLowB (one_le_pow₀ hx1) hx2 hpad0
  -- the value is small
  have hG : 64 * |(rows j).val x z + padVal P5 P7 x z j / B| < (B : ℤ) ^ 3 := by
    have hG1 : |(rows j).val x z| ≤ KB := by rw [← h5]; exact hbound _ (by omega)
    have hP1 : padVal P5 P7 x z j ≤ KB := by
      rw [← h4]; exact le_trans (le_abs_self _) (hbound _ (by omega))
    have hP2 : padVal P5 P7 x z j / B ≤ padVal P5 P7 x z j := Int.ediv_le_self _ hpad0
    have hP3 : 0 ≤ padVal P5 P7 x z j / B := Int.ediv_nonneg hpad0 hB0.le
    have habs : |(rows j).val x z + padVal P5 P7 x z j / B| ≤ 2 * KB := by
      calc |(rows j).val x z + padVal P5 P7 x z j / B|
          ≤ |(rows j).val x z| + |padVal P5 P7 x z j / B| := abs_add_le _ _
        _ = |(rows j).val x z| + padVal P5 P7 x z j / B := by rw [abs_of_nonneg hP3]
        _ ≤ KB + KB := by linarith only [hG1, hP1, hP2]
        _ = 2 * KB := by ring
    have h1 : 128 * absSum Dp * ((m : ℤ) + 1) ^ 2 * B ^ 2 < B * B ^ 2 :=
      mul_lt_mul_of_pos_right hD1 (by positivity)
    calc 64 * |(rows j).val x z + padVal P5 P7 x z j / B| ≤ 64 * (2 * KB) :=
          mul_le_mul_of_nonneg_left habs (by norm_num)
      _ = 128 * absSum Dp * ((m : ℤ) + 1) ^ 2 * B ^ 2 := by rw [hKB]; ring
      _ < B * B ^ 2 := h1
      _ = (B : ℤ) ^ 3 := by ring
  rw [hu]
  exact ⟨hwin, hG⟩

/-- The window of target `j`: `G_j + ⌊pad_j / B⌋ ≥ 0` and it is the three-digit number
read at `t_j, t_j + 1, t_j + 2`. -/
theorem window_value (hs : 3 ≤ s) {B x σ : ℕ} (hB : 64 ≤ B) (hx : 1 ≤ x) (hxB : x < B)
    (z : Fin m → ℤ) (hz0 : ∀ i, 0 ≤ z i) (hzB : ∀ i, z i ≤ B) (dum : Fin s → Fin 3 → ℤ)
    (hD1 : 128 * absSum (D m s rows P5 P7) * ((m : ℤ) + 1) ^ 2 < B)
    (High : ℤ)
    (hσ : (σ : ℤ) = ∑ p ∈ range (K m s),
      (D m s rows P5 P7 * (Cmain m x z + Cdum m s dum) ^ 2).coeff p * (B : ℤ) ^ p +
      (B : ℤ) ^ (K m s) * High)
    (j : Fin s) (hcross : ∀ q ∈ (rows j).cross, q.1 ≠ q.2.1)
    (hd0 : σ / B ^ (t m s j) % B ≤ 3) (hd1 : σ / B ^ (t m s j + 1) % B ≤ 3)
    (hd2 : σ / B ^ (t m s j + 2) % B ≤ 3) :
    0 ≤ (rows j).val x z + padVal P5 P7 x z j / B ∧
    (rows j).val x z + padVal P5 P7 x z j / B =
      ((σ / B ^ (t m s j) % B : ℕ) : ℤ) + ((σ / B ^ (t m s j + 1) % B : ℕ) : ℤ) * B +
        ((σ / B ^ (t m s j + 2) % B : ℕ) : ℤ) * B ^ 2 := by
  obtain ⟨hwin, hG⟩ :=
    window_residue rows P5 P7 hs hB hx hxB z hz0 hzB dum hD1 High hσ j hcross
  obtain ⟨hb0, hb1, hb2⟩ := window_digit_bounds hd0 hd1 hd2
  rw [hwin] at hb0 hb1 hb2
  obtain ⟨hnn, hrec⟩ := window_nonneg_of_small hB hG hb0 hb1 hb2
  refine ⟨hnn, ?_⟩
  obtain ⟨c0, c1, c2⟩ := window_digits_cast B (t m s j) σ
  rw [← hwin, c0, c1, c2] at hrec
  exact hrec

end Windows

end

end Iso

end Jones1980
