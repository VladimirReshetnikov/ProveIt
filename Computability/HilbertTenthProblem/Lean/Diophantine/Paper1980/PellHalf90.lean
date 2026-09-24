import Diophantine.Paper1980.PellDoubled
import Diophantine.Paper1980.PellRelaxedMain

/-!
# The half-parameter auxiliary Pell block (Sections 3–4 and 6 of
`HALF_PARAMETER_PELL_92_PROOF.md`)

With `R = i c²` (`R² = (A² − 1)(f² − 1)`), the block

  `u = J + jc = c + of`,  `R²(u² − y²) = 1 − y²`

is the Pell equation `(Ru)² − (R² − 1) y² = 1`.  The odd-index polynomial
`Q_h` (`χ_X(2h+1) = X · Q_h(X²)`, `Q_h(1 − A²) = (−1)^h ψ_A(2h+1)`,
`Q_h(0) = (−1)^h (2h+1)`) turns the classification `Ru = χ_R(s)`, `y = ψ_R(s)`
into `s` odd, `u = Q_h(R²)`, and the two congruences `u ≡ ±ψ_A(s) (mod f)`,
`u ≡ ±s (mod c)`; the step-down lemma then forces the main index `p = J`
(`half_index`).  Conversely (`half_witnesses`), for `J ≡ 1 (mod 4)` the
witnesses `m = 2cJ`, `f = χ_A(m)`, `i = (A² − 1) ψ_A(m)/c²`, `y = ψ_R(J)`,
`u = χ_R(J)/R`, `o = (u − c)/f`, `j = (u − J)/c` are positive integers.
-/

namespace Jones1980

open Diophantine Pell

/-! ### The odd-index polynomial -/

/-- `Q_h(T)`: `χ_X(2h+1) = X · Q_h(X²)`. -/
def Qh : ℕ → ℤ → ℤ
  | 0, _ => 1
  | 1, T => 4 * T - 3
  | (h + 2), T => (4 * T - 2) * Qh (h + 1) T - Qh h T

theorem Qh_zero (T : ℤ) : Qh 0 T = 1 := rfl
theorem Qh_one (T : ℤ) : Qh 1 T = 4 * T - 3 := rfl
theorem Qh_succ_succ (h : ℕ) (T : ℤ) : Qh (h + 2) T = (4 * T - 2) * Qh (h + 1) T - Qh h T := rfl

/-- The odd subsequence of a Pell recurrence satisfies `z_{h+2} = (4X² − 2) z_{h+1} − z_h`. -/
theorem xr_odd_rec (X : ℤ) (h : ℕ) :
    xr X (2 * (h + 2) + 1) = (4 * X ^ 2 - 2) * xr X (2 * (h + 1) + 1) - xr X (2 * h + 1) := by
  have e5 : xr X (2 * (h + 2) + 1) = 2 * X * xr X (2 * h + 4) - xr X (2 * h + 3) := by
    rw [show 2 * (h + 2) + 1 = (2 * h + 3) + 2 by ring]; exact xr_succ_succ X _
  have e4 : xr X (2 * h + 4) = 2 * X * xr X (2 * h + 3) - xr X (2 * h + 2) := xr_succ_succ X _
  have e3 : xr X (2 * h + 3) = 2 * X * xr X (2 * h + 2) - xr X (2 * h + 1) := xr_succ_succ X _
  rw [show 2 * (h + 1) + 1 = 2 * h + 3 by ring, e5, e4]
  linear_combination e3

theorem yr_odd_rec (X : ℤ) (h : ℕ) :
    yr X (2 * (h + 2) + 1) = (4 * X ^ 2 - 2) * yr X (2 * (h + 1) + 1) - yr X (2 * h + 1) := by
  have e5 : yr X (2 * (h + 2) + 1) = 2 * X * yr X (2 * h + 4) - yr X (2 * h + 3) := by
    rw [show 2 * (h + 2) + 1 = (2 * h + 3) + 2 by ring]; exact yr_succ_succ X _
  have e4 : yr X (2 * h + 4) = 2 * X * yr X (2 * h + 3) - yr X (2 * h + 2) := yr_succ_succ X _
  have e3 : yr X (2 * h + 3) = 2 * X * yr X (2 * h + 2) - yr X (2 * h + 1) := yr_succ_succ X _
  rw [show 2 * (h + 1) + 1 = 2 * h + 3 by ring, e5, e4]
  linear_combination e3

/-- `χ_X(2h+1) = X · Q_h(X²)`. -/
theorem xr_odd_eq (X : ℤ) : ∀ h, xr X (2 * h + 1) = X * Qh h (X ^ 2) := by
  refine two_step ?_ ?_ ?_
  · simp [Qh]
  · have h2 : xr X 2 = 2 * X * X - 1 := by rw [xr_succ_succ]; simp
    have h3 : xr X 3 = 2 * X * xr X 2 - xr X 1 := xr_succ_succ X 1
    show xr X 3 = X * (4 * X ^ 2 - 3)
    rw [h3, h2]; simp; ring
  · intro h ih1 ih2
    rw [xr_odd_rec, Qh_succ_succ, ih1, ih2]; ring

/-- `Q_h(1 − A²) = (−1)^h ψ_A(2h+1)`. -/
theorem Qh_eval_one_sub_sq (A : ℤ) : ∀ h, Qh h (1 - A ^ 2) = (-1) ^ h * yr A (2 * h + 1) := by
  refine two_step ?_ ?_ ?_
  · simp [Qh]
  · have h2 : yr A 2 = 2 * A := by rw [yr_succ_succ]; simp
    have h3 : yr A 3 = 2 * A * yr A 2 - yr A 1 := yr_succ_succ A 1
    show 4 * (1 - A ^ 2) - 3 = (-1) ^ 1 * yr A 3
    rw [h3, h2]; simp; ring
  · intro h ih1 ih2
    rw [yr_odd_rec, Qh_succ_succ, ih1, ih2, pow_succ, pow_succ]; ring

/-- `Q_h(0) = (−1)^h (2h+1)`. -/
theorem Qh_eval_zero : ∀ h, Qh h 0 = (-1) ^ h * (2 * h + 1) := by
  refine two_step ?_ ?_ ?_
  · simp [Qh]
  · simp [Qh]
  · intro h ih1 ih2
    rw [Qh_succ_succ, ih1, ih2, pow_succ, pow_succ]; push_cast; ring

/-- `Q_h` respects congruences. -/
theorem Qh_modEq {T T' m : ℤ} (h : T ≡ T' [ZMOD m]) : ∀ n, Qh n T ≡ Qh n T' [ZMOD m] := by
  refine two_step ?_ ?_ ?_
  · simp [Qh]
  · simp only [Qh_one]; exact ((h.mul_left 4).sub_right 3)
  · intro n ih1 ih2
    simp only [Qh_succ_succ]
    exact (((h.mul_left 4).sub_right 2).mul ih2).sub ih1

/-- `χ_0(2h) = (−1)^h`. -/
theorem xr_zero_even : ∀ h, xr 0 (2 * h) = (-1) ^ h := by
  intro h
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2 * (h + 1) = 2 * h + 2 by ring, xr_succ_succ, ih, pow_succ]; ring

/-- `χ_X(2h) ≡ (−1)^h (mod X)`. -/
theorem xr_even_modEq (X : ℤ) (h : ℕ) : xr X (2 * h) ≡ (-1) ^ h [ZMOD X] := by
  have h0 : X ≡ 0 [ZMOD X] := (Int.modEq_zero_iff_dvd).2 dvd_rfl
  have := xr_modEq h0 (2 * h)
  rwa [xr_zero_even] at this

/-- `ψ_A(n) ≡ n (mod 2)`. -/
theorem yr_modEq_two (X : ℤ) : ∀ n, yr X n ≡ n [ZMOD 2] := by
  refine two_step ?_ ?_ ?_
  · simp
  · simp
  · intro n ih1 ih2
    rw [yr_succ_succ]
    have h1 : 2 * X * yr X (n + 1) ≡ 0 [ZMOD 2] :=
      (Int.modEq_zero_iff_dvd).2 (Dvd.intro (X * yr X (n + 1)) (by ring))
    have h2 : -yr X n ≡ -(n : ℤ) [ZMOD 2] := ih1.neg
    have h3 : -(n : ℤ) ≡ ((n + 2 : ℕ) : ℤ) [ZMOD 2] := by
      rw [Int.modEq_iff_dvd]; push_cast; exact ⟨n + 1, by ring⟩
    have := (h1.add h2).trans (by simpa using h3)
    simpa [sub_eq_add_neg] using this

/-- `χ_A(2n) = 1 + 2(A² − 1) ψ_A(n)²` in `ℤ`. -/
theorem xn_two_mul_eq_yn {A : ℕ} (hA : 1 < A) (n : ℕ) :
    (xn hA (2 * n) : ℤ) = 1 + 2 * ((A : ℤ) ^ 2 - 1) * (yn hA n : ℤ) ^ 2 := by
  rw [xn_two_mul hA n]
  have h := χ_sq hA n
  simp only [Diophantine.χ, Diophantine.ψ] at h
  have hA2 : 1 ≤ A * A := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h' : ((xn hA n * xn hA n : ℕ) : ℤ) = (((A * A - 1) * yn hA n * yn hA n + 1 : ℕ) : ℤ) := by
    rw [h]
  push_cast [Nat.cast_sub hA2] at h'
  linear_combination 2 * h'

/-! ### Sufficiency: the main index is `J` -/

/-- From the half-parameter block, the main Pell index is `J`. -/
theorem half_index {A c d f i o j J p m y u : ℕ} (hA : 1 < A) (hJ1 : 1 < J) (hJc : J < c)
    (hJodd : Odd J) (hp : 0 < p) (hd : d = xn hA p) (hcp : c = yn hA p) (hf : f = xn hA m)
    (hpm : 2 * p ≤ m) (hcm : c ∣ m) (hR : i * c ^ 2 = (A ^ 2 - 1) * yn hA m) (hi : 0 < i)
    (hu : u = J + j * c) (hu' : u = c + o * f) (hy : 0 < y)
    (E17 : (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) * ((u : ℤ) ^ 2 - y ^ 2) = 1 - (y : ℤ) ^ 2) :
    p = J := by
  have hc0 : 0 < c := by omega
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hAZ : (1 : ℤ) < A := by exact_mod_cast hA
  -- `R = i c²`, `R² = (A² − 1)(f² − 1)`
  obtain ⟨R, hRdef⟩ : ∃ R, R = i * c ^ 2 := ⟨_, rfl⟩
  have hR1 : 1 < R := by
    rw [hRdef]
    have : c ^ 2 ≤ i * c ^ 2 := Nat.le_mul_of_pos_left _ hi
    have : 4 ≤ c ^ 2 := by nlinarith
    omega
  have hfsq : (f : ℤ) ^ 2 = 1 + ((A : ℤ) ^ 2 - 1) * (yn hA m : ℤ) ^ 2 := by
    have h := χ_sq hA m
    simp only [Diophantine.χ, Diophantine.ψ] at h
    have hA2' : 1 ≤ A * A := by nlinarith
    have h' : ((xn hA m * xn hA m : ℕ) : ℤ) = (((A * A - 1) * yn hA m * yn hA m + 1 : ℕ) : ℤ) := by
      rw [h]
    push_cast [Nat.cast_sub hA2'] at h'
    rw [hf]; push_cast; linear_combination h'
  have hRsq : (R : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * ((f : ℤ) ^ 2 - 1) := by
    have hRZ : (R : ℤ) = ((A : ℤ) ^ 2 - 1) * yn hA m := by
      rw [hRdef]
      have : ((i * c ^ 2 : ℕ) : ℤ) = (((A ^ 2 - 1) * yn hA m : ℕ) : ℤ) := by rw [hR]
      push_cast [Nat.cast_sub hA2] at this; exact this
    rw [hRZ, hfsq]; ring
  -- the Pell pair `(R u, y)` for the parameter `R`
  have hR2 : 1 ≤ R ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hZ : ((R : ℤ) * u) ^ 2 = 1 + ((R : ℤ) ^ 2 - 1) * y ^ 2 := by
    rw [mul_pow, hRsq]; linear_combination E17
  have hpell : (R * u) ^ 2 = 1 + (R ^ 2 - 1) * y ^ 2 := by
    have : (((R * u) ^ 2 : ℕ) : ℤ) = ((1 + (R ^ 2 - 1) * y ^ 2 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hR2]; exact hZ
    exact_mod_cast this
  obtain ⟨s, hRu, hys⟩ := eq_pell_of_sq hR1 hpell
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, yn_zero] at hys; omega
    · exact h0
  have hRZ0 : (R : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- `s` is odd
  have hsodd : Odd s := by
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    obtain ⟨h, hh⟩ := heven
    have e1 : (xn hR1 s : ℤ) ≡ (-1) ^ h [ZMOD R] := by
      rw [xn_eq_xr hR1, hh, ← two_mul]; exact xr_even_modEq (R : ℤ) h
    have e2 : (xn hR1 s : ℤ) = R * u := by rw [← hRu]; push_cast; ring
    rw [e2] at e1
    have e3 : (0 : ℤ) ≡ (-1) ^ h [ZMOD R] := by
      have : (R : ℤ) * u ≡ 0 [ZMOD R] := (Int.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
      exact this.symm.trans e1
    have hdvd : (R : ℤ) ∣ (-1) ^ h := by
      have := (Int.modEq_iff_dvd.1 e3); simpa using this
    have hdvd1 : (R : ℤ) ∣ 1 := by
      rcases neg_one_pow_eq_or ℤ h with e | e
      · rwa [e] at hdvd
      · rw [e] at hdvd; exact (dvd_neg).1 hdvd
    have : (R : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) hdvd1
    have : R = 1 := by exact_mod_cast this
    omega
  obtain ⟨h, hs⟩ := hsodd
  -- `u = Q_h(R²)`
  have hu_eq : (u : ℤ) = Qh h ((R : ℤ) ^ 2) := by
    have e1 : (xn hR1 s : ℤ) = R * Qh h ((R : ℤ) ^ 2) := by
      rw [xn_eq_xr hR1, hs]; exact xr_odd_eq (R : ℤ) h
    have e2 : (xn hR1 s : ℤ) = R * u := by rw [← hRu]; push_cast; ring
    exact mul_left_cancel₀ hRZ0 (e2.symm.trans e1)
  -- `R² ≡ 1 − A² (mod f)`
  have hRf : (R : ℤ) ^ 2 ≡ 1 - (A : ℤ) ^ 2 [ZMOD f] := by
    rw [Int.modEq_iff_dvd, hRsq]
    exact ⟨-((A : ℤ) ^ 2 - 1) * f, by ring⟩
  have hu_f : (u : ℤ) ≡ (-1) ^ h * yn hA s [ZMOD f] := by
    have := Qh_modEq hRf h
    rw [Qh_eval_one_sub_sq, ← yn_eq_yr hA, ← hs, ← hu_eq] at this
    exact this
  have hu_c : (u : ℤ) ≡ c [ZMOD f] := by
    rw [Int.modEq_iff_dvd, hu']; push_cast; exact ⟨-o, by ring⟩
  -- `ψ_A(s)² ≡ ψ_A(p)² (mod f)` and the step-down
  have hsq : (yn hA s : ℤ) ^ 2 ≡ (yn hA p : ℤ) ^ 2 [ZMOD f] := by
    have h1 : (-1 : ℤ) ^ h * yn hA s ≡ c [ZMOD f] := hu_f.symm.trans hu_c
    have h2 := h1.pow 2
    have e : ((-1 : ℤ) ^ h * yn hA s) ^ 2 = (yn hA s : ℤ) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm h 2, pow_mul]; simp
    rw [e, hcp] at h2; exact h2
  have hstep : (xn hA m : ℤ) ∣ (xn hA (2 * s) : ℤ) - xn hA (2 * p) := by
    rw [← hf, xn_two_mul_eq_yn hA s, xn_two_mul_eq_yn hA p]
    have := (Int.modEq_iff_dvd.1 hsq.symm)
    obtain ⟨k, hk⟩ := this
    exact ⟨2 * ((A : ℤ) ^ 2 - 1) * k, by linear_combination 2 * ((A : ℤ) ^ 2 - 1) * hk⟩
  have hsp := step_down hA hp hpm (Or.inl hstep)
  have hcmZ : (c : ℤ) ∣ m := by exact_mod_cast hcm
  have hsp' : (c : ℤ) ∣ (s : ℤ) - p ∨ (c : ℤ) ∣ (s : ℤ) + p := by
    rcases hsp with hh | hh
    · exact Or.inl (dvd_trans hcmZ hh)
    · exact Or.inr (dvd_trans hcmZ hh)
  -- `u ≡ (−1)^h s (mod c)` and `u ≡ J (mod c)`
  have hcR : (c : ℤ) ∣ (R : ℤ) ^ 2 := by
    rw [hRdef]; push_cast; exact ⟨i ^ 2 * c ^ 3, by ring⟩
  have hu_cc : (u : ℤ) ≡ (-1) ^ h * s [ZMOD c] := by
    have h0 : (R : ℤ) ^ 2 ≡ 0 [ZMOD c] := (Int.modEq_zero_iff_dvd).2 hcR
    have := Qh_modEq h0 h
    rw [Qh_eval_zero, ← hu_eq] at this
    rw [hs]; push_cast; exact this
  have hu_J : (u : ℤ) ≡ J [ZMOD c] := by
    rw [Int.modEq_iff_dvd, hu]; push_cast; exact ⟨-j, by ring⟩
  have hJs : (J : ℤ) ≡ (-1) ^ h * s [ZMOD c] := hu_J.symm.trans hu_cc
  -- hence `c ∣ J − p` or `c ∣ J + p`
  have hJp : (c : ℤ) ∣ (J : ℤ) - p ∨ (c : ℤ) ∣ (J : ℤ) + p := by
    have hJs' := Int.modEq_iff_dvd.1 hJs   -- c ∣ (-1)^h s − J
    rcases neg_one_pow_eq_or ℤ h with e | e <;> rw [e] at hJs' <;> rcases hsp' with hh | hh
    · left; obtain ⟨k1, hk1⟩ := hh; obtain ⟨k2, hk2⟩ := hJs'
      exact ⟨k1 - k2, by linear_combination hk1 - hk2⟩
    · right; obtain ⟨k1, hk1⟩ := hh; obtain ⟨k2, hk2⟩ := hJs'
      exact ⟨k1 - k2, by linear_combination hk1 - hk2⟩
    · right; obtain ⟨k1, hk1⟩ := hh; obtain ⟨k2, hk2⟩ := hJs'
      exact ⟨-k1 - k2, by linear_combination -hk1 - hk2⟩
    · left; obtain ⟨k1, hk1⟩ := hh; obtain ⟨k2, hk2⟩ := hJs'
      exact ⟨-k1 - k2, by linear_combination -hk1 - hk2⟩
  -- `p ≥ 2`, so `p < c`
  have hp2 : 2 ≤ p := by
    by_contra hlt
    have : p = 1 := by omega
    rw [this, yn_one] at hcp; omega
  have hpc : p < c := by rw [hcp]; exact lt_yn_of_two_le hA hp2
  have hJZ : (0 : ℤ) < J := by exact_mod_cast (show 0 < J by omega)
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hJcZ : (J : ℤ) < c := by exact_mod_cast hJc
  have hpcZ : (p : ℤ) < c := by exact_mod_cast hpc
  rcases hJp with hh | hh
  · have : (J : ℤ) - p = 0 := Int.eq_zero_of_abs_lt_dvd hh (by rw [abs_lt]; constructor <;> linarith)
    have : (p : ℤ) = J := by linarith
    exact_mod_cast this
  · -- `J + p = c`, contradicting parity
    exfalso
    obtain ⟨k, hk⟩ := hh
    have hk1 : k = 1 := by
      have hcZ : (0 : ℤ) < c := by exact_mod_cast hc0
      have h1 : 0 < k := by
        by_contra hneg; push Not at hneg
        have : (c : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcZ.le hneg
        linarith
      have h2 : k < 2 := by
        by_contra hge; push Not at hge
        have : (c : ℤ) * 2 ≤ c * k := mul_le_mul_of_nonneg_left hge hcZ.le
        linarith
      omega
    rw [hk1, mul_one] at hk
    -- parity: `c = ψ_A(p) ≡ p`, `J` odd
    have hpar : (c : ℤ) ≡ p [ZMOD 2] := by
      rw [hcp, yn_eq_yr hA]; exact yr_modEq_two (A : ℤ) p
    have hJodd' : (J : ℤ) ≡ 1 [ZMOD 2] := by
      obtain ⟨t, ht⟩ := hJodd
      rw [Int.modEq_iff_dvd]; push_cast [ht]; exact ⟨-t, by ring⟩
    have : (J : ℤ) + p ≡ p [ZMOD 2] := by rw [hk]; exact hpar
    have h2 : (J : ℤ) ≡ 0 [ZMOD 2] := by
      have := this.sub_right (p : ℤ); simpa using this
    have := hJodd'.symm.trans h2
    have : (1 : ℤ) % 2 = 0 % 2 := this
    norm_num at this

/-! ### Necessity: the witnesses -/

/-- The witnesses of the half-parameter block for `J ≡ 1 (mod 4)`. -/
theorem half_witnesses {A J : ℕ} (hA : 1 < A) (hJ1 : 1 < J) (hJ4 : J % 4 = 1) :
    ∃ f i o j y : ℕ, 0 < f ∧ 0 < i ∧ 0 < o ∧ 0 < j ∧ 0 < y ∧
      (i * yn hA J ^ 2) ^ 2 = (A ^ 2 - 1) * (f ^ 2 - 1) ∧
      J + j * yn hA J = yn hA J + o * f ∧
      (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) * (((J : ℤ) + j * yn hA J) ^ 2 - (y : ℤ) ^ 2) =
        1 - (y : ℤ) ^ 2 := by
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨c, hc⟩ : ∃ c, c = yn hA J := ⟨_, rfl⟩
  have hJc : J < c := by rw [hc]; exact lt_yn_of_two_le hA (by omega)
  have hc2 : 2 ≤ c := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * (J * c) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  obtain ⟨f, hf⟩ : ∃ f, f = xn hA m := ⟨_, rfl⟩
  have hf0 : 0 < f := by rw [hf]; exact xn_pos' hA m
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, yn hA m = c ^ 2 * i₀ := by
    obtain ⟨i₀, hi₀⟩ := sq_dvd_yn_two_mul hA (J := J)
    exact ⟨i₀, by rw [hm, hc, hi₀]⟩
  have hym : 0 < yn hA m := JSWW1976.ψ_pos_of_pos hA hm0
  have hi₀0 : 0 < i₀ := by
    rcases Nat.eq_zero_or_pos i₀ with h0 | h0
    · rw [h0, mul_zero] at hi₀; omega
    · exact h0
  obtain ⟨i, hi⟩ : ∃ i, i = (A ^ 2 - 1) * i₀ := ⟨_, rfl⟩
  have hi0 : 0 < i := by
    have hD : 0 < A ^ 2 - 1 := by
      have : 2 ≤ A ^ 2 := by nlinarith
      omega
    rw [hi]; exact Nat.mul_pos hD hi₀0
  obtain ⟨R, hRdef⟩ : ∃ R, R = i * c ^ 2 := ⟨_, rfl⟩
  have hRm : R = (A ^ 2 - 1) * yn hA m := by rw [hRdef, hi, hi₀]; ring
  have hR1 : 1 < R := by
    rw [hRdef]
    have : c ^ 2 ≤ i * c ^ 2 := Nat.le_mul_of_pos_left _ hi0
    have : 4 ≤ c ^ 2 := by nlinarith
    omega
  have hRc : c ^ 2 ≤ R := by rw [hRdef]; exact Nat.le_mul_of_pos_left _ hi0
  -- `f² = 1 + (A² − 1) ψ_A(m)²`
  have hfsq : f ^ 2 = 1 + (A ^ 2 - 1) * yn hA m ^ 2 := by
    have h := χ_sq hA m
    simp only [Diophantine.χ, Diophantine.ψ] at h
    rw [hf, sq, h, sq, sq]
    have : (A * A - 1) = A ^ 2 - 1 := by rw [sq]
    rw [this]; ring
  -- `E16`
  have E16 : (i * c ^ 2) ^ 2 = (A ^ 2 - 1) * (f ^ 2 - 1) := by
    rw [← hRdef, hRm, hfsq, Nat.add_sub_cancel_left]; ring
  have hRsq : (R : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * ((f : ℤ) ^ 2 - 1) := by
    have : ((R ^ 2 : ℕ) : ℤ) = (((A ^ 2 - 1) * (f ^ 2 - 1) : ℕ) : ℤ) := by rw [hRdef, E16]
    have hf2 : 1 ≤ f ^ 2 := Nat.one_le_pow _ _ hf0
    push_cast [Nat.cast_sub hA2, Nat.cast_sub hf2] at this
    exact this
  -- the index `J = 2h + 1` with `h` even
  obtain ⟨h, hh⟩ : ∃ h, J = 2 * h + 1 := ⟨J / 2, by omega⟩
  have hheven : Even h := ⟨h / 2, by omega⟩
  -- `y = ψ_R(J)`, `u = Q_h(R²) = χ_R(J)/R`
  obtain ⟨y, hy⟩ : ∃ y, y = yn hR1 J := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; exact JSWW1976.ψ_pos_of_pos hR1 (by omega)
  have hxQ : (xn hR1 J : ℤ) = R * Qh h ((R : ℤ) ^ 2) := by
    rw [xn_eq_xr hR1, hh]; exact xr_odd_eq (R : ℤ) h
  have hQpos : 0 < Qh h ((R : ℤ) ^ 2) := by
    have h1 : (0 : ℤ) < xn hR1 J := by exact_mod_cast xn_pos' hR1 J
    have h2 : (0 : ℤ) < R := by exact_mod_cast (show 0 < R by omega)
    rw [hxQ] at h1
    exact pos_of_mul_pos_right h1 h2.le
  obtain ⟨u, hu⟩ : ∃ u : ℕ, (u : ℤ) = Qh h ((R : ℤ) ^ 2) :=
    ⟨(Qh h ((R : ℤ) ^ 2)).toNat, Int.toNat_of_nonneg hQpos.le⟩
  have hRu : R * u = xn hR1 J := by
    have : ((R * u : ℕ) : ℤ) = xn hR1 J := by push_cast; rw [hu, hxQ]
    exact_mod_cast this
  -- `E17`
  have hpell := χ_sq hR1 J
  simp only [Diophantine.χ, Diophantine.ψ] at hpell
  have E17 : (((A : ℤ) ^ 2 - 1) * (f ^ 2 - 1)) * ((u : ℤ) ^ 2 - (y : ℤ) ^ 2) = 1 - (y : ℤ) ^ 2 := by
    rw [← hRsq]
    have hR2 : 1 ≤ R * R := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h' : ((xn hR1 J * xn hR1 J : ℕ) : ℤ) = (((R * R - 1) * yn hR1 J * yn hR1 J + 1 : ℕ) : ℤ) := by
      rw [hpell]
    rw [← hRu, ← hy] at h'
    push_cast [Nat.cast_sub hR2] at h'
    linear_combination h'
  -- congruences: `u ≡ c (mod f)`, `u ≡ J (mod c)`
  have hRf : (R : ℤ) ^ 2 ≡ 1 - (A : ℤ) ^ 2 [ZMOD f] := by
    rw [Int.modEq_iff_dvd, hRsq]
    exact ⟨-((A : ℤ) ^ 2 - 1) * f, by ring⟩
  have huc : (u : ℤ) ≡ c [ZMOD f] := by
    have := Qh_modEq hRf h
    rw [Qh_eval_one_sub_sq, ← yn_eq_yr hA, ← hh, ← hc, hheven.neg_one_pow, one_mul, ← hu] at this
    exact this
  have hcR : (c : ℤ) ∣ (R : ℤ) ^ 2 := by
    rw [hRdef]; push_cast; exact ⟨i ^ 2 * c ^ 3, by ring⟩
  have huJ : (u : ℤ) ≡ J [ZMOD c] := by
    have h0 : (R : ℤ) ^ 2 ≡ 0 [ZMOD c] := (Int.modEq_zero_iff_dvd).2 hcR
    have := Qh_modEq h0 h
    rw [Qh_eval_zero, hheven.neg_one_pow, one_mul, ← hu] at this
    push_cast at this
    rw [hh]; push_cast; exact this
  -- sizes: `u ≥ R^(J−1) ≥ R ≥ c² > c > J`
  have hu_ge : R ≤ u := by
    have h1 : R ^ J ≤ R * u := by rw [hRu]; exact xn_ge_a_pow hR1 J
    have h2 : R * R ≤ R ^ J := by
      rw [← sq]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have : R * R ≤ R * u := le_trans h2 h1
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hcu : c < u := by nlinarith
  have hJu : J < u := by omega
  -- the quotients `o`, `j`
  have hf_dvd : f ∣ u - c := by
    have h1 : (f : ℤ) ∣ (u : ℤ) - c := (Int.modEq_iff_dvd.1 huc.symm)
    have : ((u - c : ℕ) : ℤ) = (u : ℤ) - c := by push_cast [Nat.cast_sub hcu.le]; rfl
    rw [← this] at h1
    exact_mod_cast h1
  have hc_dvd : c ∣ u - J := by
    have h1 : (c : ℤ) ∣ (u : ℤ) - J := (Int.modEq_iff_dvd.1 huJ.symm)
    have : ((u - J : ℕ) : ℤ) = (u : ℤ) - J := by push_cast [Nat.cast_sub hJu.le]; rfl
    rw [← this] at h1
    exact_mod_cast h1
  obtain ⟨o, ho⟩ := hf_dvd
  obtain ⟨j, hj⟩ := hc_dvd
  have ho0 : 0 < o := by
    rcases Nat.eq_zero_or_pos o with h0 | h0
    · rw [h0, mul_zero] at ho; omega
    · exact h0
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, mul_zero] at hj; omega
    · exact h0
  have hu1 : u = c + o * f := by rw [mul_comm]; omega
  have hu2 : u = J + j * c := by rw [mul_comm]; omega
  refine ⟨f, i, o, j, y, hf0, hi0, ho0, hj0, hy0, ?_, ?_, ?_⟩
  · rw [← hc]; exact E16
  · rw [← hc, ← hu2, hu1]
  · rw [← hc]
    have : ((J + j * c : ℕ) : ℤ) = u := by rw [← hu2]
    push_cast at this
    rw [this]; exact E17

end Jones1980
