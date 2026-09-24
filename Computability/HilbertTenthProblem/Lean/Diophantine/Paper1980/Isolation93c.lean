import Diophantine.Paper1980.Isolation93b

/-!
# Coefficient isolation, part 3: the values in the window of a target

For `Q = C_main²` and a position `p` in the window `[t_j − 5, t_j + 2]` of
target `j`, only the exponents of band `j` contribute to `[X^p](D · Q)`
(`coeff_band_only`), and the residue classes modulo six of those exponents
give the values

* at `t_j`: the value of row `j`;
* at `t_j − 3`: `x²`;
* at `t_j − 1`: `x² + 2x Σ_{q ∈ P} z_q` if `j` carries the padding set `P`, else `0`;
* at `t_j − 5, t_j − 4, t_j − 2, t_j + 1, t_j + 2`: `0`.
-/

namespace Jones1980

namespace Iso

open Polynomial Layout

noncomputable section

section Band

variable {m s : ℕ} (rows : Fin s → Row m) (P5 P7 : Finset (Fin m)) (x : ℤ) (z : Fin m → ℤ)

/-- Band separation in the form used here: an exponent `d'` of band `k`
(`d' ≤ t_k ≤ d' + 2M`) contributing to a window position of target `j` forces `k = j`. -/
theorem band_unique' {j k p d' : ℕ}
    (hp1 : t m s j ≤ p + 5) (hp2 : p ≤ t m s j + 2)
    (hd1 : t m s k ≤ d' + 2 * M m) (hd2 : d' ≤ t m s k)
    (hpd : d' ≤ p ∧ p ≤ d' + 2 * M m) : k = j := by
  by_contra hne
  have hd0 : d0 m = 4 * M m + 6 := rfl
  have hM := M_pos m
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := t_sub_ge (m := m) (s := s) hlt
    omega
  · have := t_sub_ge (m := m) (s := s) hgt
    omega

/-- `contrib c e p Q` vanishes unless `e ≤ p`, `6 ∣ p − e` and `p − e ≤ 2M`. -/
theorem contrib_eq_zero {e p : ℕ} {cz : ℤ}
    (h : ¬ (e ≤ p ∧ 6 ∣ p - e ∧ p - e ≤ 2 * M m)) :
    contrib cz e p (Cmain m x z ^ 2) = 0 := by
  unfold contrib
  split_ifs with hep
  · by_cases hdvd : 6 ∣ p - e
    · by_cases hle : p - e ≤ 2 * M m
      · exact absurd ⟨hep, hdvd, hle⟩ h
      · rw [coeff_Cmain_sq_of_gt x z (by omega), mul_zero]
    · rw [coeff_Cmain_sq_of_not_dvd x z hdvd, mul_zero]
  · rfl

/-- A band-`k` exponent contributes nothing to the window of `j ≠ k`. -/
theorem contrib_other_band {j k p e : ℕ} {cz : ℤ} (hjk : k ≠ j)
    (hp1 : t m s j ≤ p + 5) (hp2 : p ≤ t m s j + 2)
    (he1 : t m s k ≤ e + 2 * M m) (he2 : e ≤ t m s k) :
    contrib cz e p (Cmain m x z ^ 2) = 0 := by
  apply contrib_eq_zero x z
  rintro ⟨hep, -, hle⟩
  exact hjk (band_unique' (m := m) (s := s) hp1 hp2 he1 he2 ⟨hep, by omega⟩)

/-- The coefficient of `X^p` in `rowPoly · Q` as a sum of contributions. -/
theorem coeff_rowPoly_mul (j : ℕ) (R : Row m) (Q : ℤ[X]) (p : ℕ) :
    (rowPoly m s j R * Q).coeff p = (R.terms.map fun q => contrib q.2 (t m s j - q.1) p Q).sum := by
  unfold rowPoly
  rw [← List.sum_map_mul_right, coeff_list_sum]
  congr 1
  apply List.map_congr_left
  intro q _
  rw [coeff_monomial_mul]

theorem coeff_resetPoly_mul (j : ℕ) (Q : ℤ[X]) (p : ℕ) :
    (resetPoly m s j * Q).coeff p = contrib 1 (t m s j - 3) p Q := by
  unfold resetPoly; rw [coeff_X_pow_mul_eq]

theorem coeff_padPoly_mul (j : ℕ) (P : Finset (Fin m)) (Q : ℤ[X]) (p : ℕ) :
    (padPoly m s j P * Q).coeff p =
      contrib 1 (t m s j - 1) p Q + ∑ q ∈ P, contrib 1 (t m s j - 1 - v q) p Q := by
  unfold padPoly
  rw [add_mul, coeff_add, coeff_X_pow_mul_eq, Finset.sum_mul, finsetSum_coeff]
  congr 1
  exact Finset.sum_congr rfl fun q _ => by rw [coeff_X_pow_mul_eq]

/-- Only band `j` contributes to a position of the window of target `j`. -/
theorem coeff_band_only (hs : 3 ≤ s) (j : Fin s) (p : ℕ)
    (hp1 : t m s j ≤ p + 5) (hp2 : p ≤ t m s j + 2) :
    (D m s rows P5 P7 * Cmain m x z ^ 2).coeff p =
      ((rows j).terms.map fun q => contrib q.2 (t m s j - q.1) p (Cmain m x z ^ 2)).sum +
      contrib 1 (t m s j - 3) p (Cmain m x z ^ 2) +
      (if (j : ℕ) = s - 2 then
        contrib 1 (t m s (s - 2) - 1) p (Cmain m x z ^ 2) +
          ∑ q ∈ P5, contrib 1 (t m s (s - 2) - 1 - v q) p (Cmain m x z ^ 2) else 0) +
      (if (j : ℕ) = s - 1 then
        contrib 1 (t m s (s - 1) - 1) p (Cmain m x z ^ 2) +
          ∑ q ∈ P7, contrib 1 (t m s (s - 1) - 1 - v q) p (Cmain m x z ^ 2) else 0) := by
  have hM := M_pos m
  have hM6 : 6 ≤ M m := by
    unfold M; have := Nat.one_le_pow (m - 1) 3 (by norm_num); omega
  unfold D
  rw [add_mul, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul, coeff_add, coeff_add, coeff_add,
    finsetSum_coeff, finsetSum_coeff]
  -- the row sums: only row `j`
  have hrows : (∑ k : Fin s, (rowPoly m s k (rows k) * Cmain m x z ^ 2).coeff p) =
      ((rows j).terms.map fun q => contrib q.2 (t m s j - q.1) p (Cmain m x z ^ 2)).sum := by
    rw [Finset.sum_eq_single j]
    · rw [coeff_rowPoly_mul]
    · intro k _ hkj
      rw [coeff_rowPoly_mul]
      apply List.sum_eq_zero
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      have hw := (Row.terms_weight (rows k) q hq).2
      apply contrib_other_band x z (Fin.val_ne_of_ne hkj) hp1 hp2
      · unfold M; omega
      · omega
    · simp
  -- the reset sums: only target `j`
  have hresets : (∑ k : Fin s, (resetPoly m s k * Cmain m x z ^ 2).coeff p) =
      contrib 1 (t m s j - 3) p (Cmain m x z ^ 2) := by
    rw [Finset.sum_eq_single j]
    · rw [coeff_resetPoly_mul]
    · intro k _ hkj
      rw [coeff_resetPoly_mul]
      apply contrib_other_band x z (Fin.val_ne_of_ne hkj) hp1 hp2
      · omega
      · omega
    · simp
  -- the paddings
  have hpad : ∀ (k : ℕ) (P : Finset (Fin m)), k < s →
      (padPoly m s k P * Cmain m x z ^ 2).coeff p =
        if (j : ℕ) = k then contrib 1 (t m s k - 1) p (Cmain m x z ^ 2) +
          ∑ q ∈ P, contrib 1 (t m s k - 1 - v q) p (Cmain m x z ^ 2) else 0 := by
    intro k P hk
    rw [coeff_padPoly_mul]
    split_ifs with hjk
    · rfl
    · rw [contrib_other_band x z (fun h => hjk h.symm) hp1 hp2 (by omega) (by omega)]
      rw [Finset.sum_eq_zero]
      · simp
      · intro q _
        have := v_le_M q.2
        exact contrib_other_band x z (fun h => hjk h.symm) hp1 hp2 (by omega) (by omega)
  rw [hrows, hresets, hpad (s - 2) P5 (by omega), hpad (s - 1) P7 (by omega)]

end Band

end

end Iso

end Jones1980
