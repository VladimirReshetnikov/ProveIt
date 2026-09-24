import Diophantine.Paper1980.Csq90

/-!
# Coefficient isolation for the 90-operation layout, part 1: bands

The coefficient of `X^p` in `D · C²` is the sum of the *contributions*
`contrib c e p (C²) = c · [X^(p−e)] C²` of the terms `c X^e` of `D`
(`coeff_D_mul`).  A contribution vanishes unless `p − e` is the weight of a
monomial of degree at most two, so `e ≤ p ≤ e + 2M` and `8 ∣ p − e`; the band
spacing `d₀ = 12M + 8` then leaves, at the positions `t_j − 4M − 6 ≤ p ≤ t_j + 2`
of band `j`, only the terms of row `j`, its helper complements, the resets of
its starts, and (for the last band) the padding (`coeff_band_only`).
-/

namespace Jones1980

namespace L90

open Polynomial Finset
open Layout (Row)
open Iso (contrib coeff_monomial_mul coeff_X_pow_mul_eq coeff_list_sum coeff_mul_eq_zero_of_lt)

noncomputable section

variable {m s : ℕ} (rows : Fin s → Row m) (hel : Fin s → Fin 3 → Fin m) (PX : Finset (Fin m))
  (x : ℤ) (z : Fin m → ℤ)

/-! ### Contributions -/

theorem coeff_rowPoly_mul (j : ℕ) (R : Row m) (Q : ℤ[X]) (p : ℕ) :
    (rowPoly s j R * Q).coeff p =
      ((terms R).map fun q => contrib q.2 (t m s j - W q.1) p Q).sum := by
  unfold rowPoly
  rw [← List.sum_map_mul_right, coeff_list_sum]
  congr 1
  apply List.map_congr_left
  intro q _
  rw [coeff_monomial_mul]

theorem coeff_helpPoly_mul (j : ℕ) (R : Row m) (P : Fin 3 → Fin m) (Q : ℤ[X]) (p : ℕ) :
    (helpPoly s j R P * Q).coeff p =
      ((negs R).map fun μ =>
        ((pairs P).map fun π => contrib 1 (t m s j - W μ - W π) p Q).sum).sum := by
  unfold helpPoly
  rw [← List.sum_map_mul_right, coeff_list_sum]
  congr 1
  apply List.map_congr_left
  intro μ _
  rw [← List.sum_map_mul_right, coeff_list_sum]
  congr 1
  apply List.map_congr_left
  intro π _
  rw [coeff_X_pow_mul_eq]

theorem coeff_resetPoly_mul (Q : ℤ[X]) (p : ℕ) :
    (resetPoly s rows * Q).coeff p = ∑ r ∈ Rset s rows, contrib 1 (r - 4) p Q := by
  unfold resetPoly
  rw [Finset.sum_mul, finsetSum_coeff]
  exact Finset.sum_congr rfl fun r _ => by rw [coeff_X_pow_mul_eq]

theorem coeff_padPoly_mul (Q : ℤ[X]) (p : ℕ) :
    (padPoly s PX * Q).coeff p = ∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) p Q := by
  unfold padPoly
  rw [Finset.sum_mul, finsetSum_coeff]
  exact Finset.sum_congr rfl fun h _ => by rw [coeff_X_pow_mul_eq]

theorem coeff_D_mul (Q : ℤ[X]) (p : ℕ) :
    (D s rows hel PX * Q).coeff p =
      ∑ j : Fin s, ((terms (rows j)).map fun q => contrib q.2 (t m s j - W q.1) p Q).sum +
      ∑ j : Fin s, ((negs (rows j)).map fun μ =>
        ((pairs (hel j)).map fun π => contrib 1 (t m s j - W μ - W π) p Q).sum).sum +
      ∑ r ∈ Rset s rows, contrib 1 (r - 4) p Q +
      ∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) p Q := by
  unfold D
  rw [add_mul, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul, coeff_add, coeff_add, coeff_add,
    finsetSum_coeff, finsetSum_coeff, coeff_resetPoly_mul, coeff_padPoly_mul]
  have h1 : ∑ j : Fin s, (rowPoly s j (rows j) * Q).coeff p =
      ∑ j : Fin s, ((terms (rows j)).map fun q => contrib q.2 (t m s j - W q.1) p Q).sum :=
    Finset.sum_congr rfl fun j _ => coeff_rowPoly_mul j _ Q p
  have h2 : ∑ j : Fin s, (helpPoly s j (rows j) (hel j) * Q).coeff p =
      ∑ j : Fin s, ((negs (rows j)).map fun μ =>
        ((pairs (hel j)).map fun π => contrib 1 (t m s j - W μ - W π) p Q).sum).sum :=
    Finset.sum_congr rfl fun j _ => coeff_helpPoly_mul j _ _ Q p
  rw [h1, h2]

/-! ### Vanishing of contributions -/

theorem contrib_eq_zero_of_not_W {c : ℤ} {e p : ℕ}
    (h : ∀ ν : Multiset (Fin m), Multiset.card ν ≤ 2 → e + W ν ≠ p) :
    contrib c e p (Cmain x z ^ 2) = 0 := by
  unfold contrib
  split_ifs with hep
  · rw [coeff_Cmain_sq_eq_zero x z (fun ν hν hW => h ν hν (by omega)), mul_zero]
  · rfl

theorem contrib_ne_zero_imp {c : ℤ} {e p : ℕ} (h : contrib c e p (Cmain x z ^ 2) ≠ 0) :
    e ≤ p ∧ ∃ ν : Multiset (Fin m), Multiset.card ν ≤ 2 ∧ p = e + W ν := by
  by_contra hne
  apply h
  apply contrib_eq_zero_of_not_W
  intro ν hν hp
  exact hne ⟨by omega, ν, hν, hp.symm⟩

theorem contrib_eq_zero_of_far {c : ℤ} {e p : ℕ} (h : ¬ (e ≤ p ∧ p ≤ e + 2 * M m)) :
    contrib c e p (Cmain x z ^ 2) = 0 := by
  by_contra hne
  obtain ⟨hep, ν, hν, hp⟩ := contrib_ne_zero_imp x z hne
  have := W_le ν
  have : Multiset.card ν * M m ≤ 2 * M m := Nat.mul_le_mul_right _ hν
  exact h ⟨hep, by omega⟩

theorem contrib_eq_zero_of_mod {c : ℤ} {e p : ℕ} (he : 8 ∣ e) (hp : ¬ 8 ∣ p) :
    contrib c e p (Cmain x z ^ 2) = 0 := by
  by_contra hne
  obtain ⟨hep, ν, hν, hpe⟩ := contrib_ne_zero_imp x z hne
  exact hp (hpe ▸ dvd_add he (eight_dvd_W ν))

/-- A contribution at `p ≥ e` with `p − e` a weight. -/
theorem contrib_of_le {c : ℤ} {e p : ℕ} (hep : e ≤ p) :
    contrib c e p (Cmain x z ^ 2) = c * (Cmain x z ^ 2).coeff (p - e) := by
  unfold contrib; rw [if_pos hep]

theorem contrib_other_band {j k p e : ℕ} {c : ℤ} (hjk : k ≠ j)
    (hp1 : t m s j ≤ p + 4 * M m + 6) (hp2 : p ≤ t m s j + 2)
    (he1 : t m s k ≤ e + 4 * M m + 4) (he2 : e ≤ t m s k) :
    contrib c e p (Cmain x z ^ 2) = 0 := by
  apply contrib_eq_zero_of_far x z
  intro hpe
  exact band_unique (m := m) (s := s) hjk hp1 hp2 he1 he2 hpe

/-! ### Exponent bounds -/

theorem W_le_two_M_of_mem_terms {R : Row m} {q : Multiset (Fin m) × ℤ} (hq : q ∈ terms R) :
    W q.1 ≤ 2 * M m := by
  have h1 := W_le q.1
  have h2 := card_le_two_of_mem_terms hq
  have : Multiset.card q.1 * M m ≤ 2 * M m := Nat.mul_le_mul_right _ h2
  omega

theorem W_le_two_M_of_mem_negs {R : Row m} {μ : Multiset (Fin m)} (hμ : μ ∈ negs R) :
    W μ ≤ 2 * M m := by
  obtain ⟨c, hc, _⟩ := (mem_negs).1 hμ
  exact W_le_two_M_of_mem_terms hc

theorem W_le_two_M_of_mem_pairs {P : Fin 3 → Fin m} {π : Multiset (Fin m)} (hπ : π ∈ pairs P) :
    W π ≤ 2 * M m := by
  have h1 := W_le π; rw [card_of_mem_pairs hπ] at h1; exact h1

theorem starts_bounds {j : Fin s} {r : ℕ} (hr : r ∈ starts s rows j) :
    t m s j ≤ r + 2 * M m ∧ r ≤ t m s j := by
  rcases (mem_starts s rows).1 hr with rfl | ⟨μ, hμ, rfl⟩
  · exact ⟨by omega, le_rfl⟩
  · have := W_le_two_M_of_mem_negs hμ; have := t_ge m s j; constructor <;> omega

theorem eight_dvd_of_mem_starts {j : Fin s} {r : ℕ} (hr : r ∈ starts s rows j) : 8 ∣ r := by
  rcases (mem_starts s rows).1 hr with rfl | ⟨μ, hμ, rfl⟩
  · exact eight_dvd_t m s j
  · exact Nat.dvd_sub (eight_dvd_t m s j) (eight_dvd_W μ)

theorem Rset_bounds {r : ℕ} (hr : r ∈ Rset s rows) : t m s 0 ≤ r + 2 * M m ∧ r ≤ tl m s := by
  obtain ⟨j, hj⟩ := (mem_Rset s rows).1 hr
  obtain ⟨h1, h2⟩ := starts_bounds rows hj
  exact ⟨le_trans (t_mono (Nat.zero_le _)) h1, le_trans h2 (t_le_tl j)⟩

/-! ### Only one band -/

/-- Only band `j` contributes to a position of a window of band `j`. -/
theorem coeff_band_only (hL : LayoutOk s rows hel) (j : Fin s) (p : ℕ)
    (hp1 : t m s j ≤ p + 4 * M m + 6) (hp2 : p ≤ t m s j + 2) :
    (D s rows hel PX * Cmain x z ^ 2).coeff p =
      ((terms (rows j)).map fun q => contrib q.2 (t m s j - W q.1) p (Cmain x z ^ 2)).sum +
      ((negs (rows j)).map fun μ =>
        ((pairs (hel j)).map fun π =>
          contrib 1 (t m s j - W μ - W π) p (Cmain x z ^ 2)).sum).sum +
      ∑ r ∈ starts s rows j, contrib 1 (r - 4) p (Cmain x z ^ 2) +
      (if (j : ℕ) = s - 1 then
        ∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) p (Cmain x z ^ 2) else 0) := by
  rw [coeff_D_mul]
  have htj := t_ge m s j
  -- the rows: only row `j`
  have hrows : (∑ k : Fin s,
      ((terms (rows k)).map fun q => contrib q.2 (t m s k - W q.1) p (Cmain x z ^ 2)).sum) =
      ((terms (rows j)).map fun q => contrib q.2 (t m s j - W q.1) p (Cmain x z ^ 2)).sum := by
    rw [Finset.sum_eq_single j]
    · intro k _ hkj
      apply List.sum_eq_zero
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      have hw := W_le_two_M_of_mem_terms hq
      have htk := t_ge m s k
      exact contrib_other_band x z (Fin.val_ne_of_ne hkj) hp1 hp2 (by omega) (by omega)
    · simp
  -- the helper complements: only row `j`
  have hhelp : (∑ k : Fin s, ((negs (rows k)).map fun μ =>
      ((pairs (hel k)).map fun π => contrib 1 (t m s k - W μ - W π) p (Cmain x z ^ 2)).sum).sum) =
      ((negs (rows j)).map fun μ =>
        ((pairs (hel j)).map fun π =>
          contrib 1 (t m s j - W μ - W π) p (Cmain x z ^ 2)).sum).sum := by
    rw [Finset.sum_eq_single j]
    · intro k _ hkj
      apply List.sum_eq_zero
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨μ, hμ, rfl⟩ := hy
      apply List.sum_eq_zero
      intro y' hy'
      rw [List.mem_map] at hy'
      obtain ⟨π, hπ, rfl⟩ := hy'
      have hw := W_le_two_M_of_mem_negs hμ
      have hw' := W_le_two_M_of_mem_pairs hπ
      have htk := t_ge m s k
      exact contrib_other_band x z (Fin.val_ne_of_ne hkj) hp1 hp2 (by omega) (by omega)
    · simp
  -- the resets: only the starts of `j`
  have hreset : (∑ r ∈ Rset s rows, contrib 1 (r - 4) p (Cmain x z ^ 2)) =
      ∑ r ∈ starts s rows j, contrib 1 (r - 4) p (Cmain x z ^ 2) := by
    symm
    apply Finset.sum_subset
    · intro r hr; exact (mem_Rset s rows).2 ⟨j, hr⟩
    · intro r hr hrj
      obtain ⟨k, hk⟩ := (mem_Rset s rows).1 hr
      have hkj : k ≠ j := fun h => hrj (h ▸ hk)
      obtain ⟨hb1, hb2⟩ := starts_bounds rows hk
      have htk := t_ge m s k
      exact contrib_other_band x z (Fin.val_ne_of_ne hkj) hp1 hp2 (by omega) (by omega)
  -- the padding: only the last band
  have hpad : (∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) p (Cmain x z ^ 2)) =
      if (j : ℕ) = s - 1 then
        ∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) p (Cmain x z ^ 2) else 0 := by
    split_ifs with hj
    · rfl
    · apply Finset.sum_eq_zero
      intro h _
      have hv := v_le_M h.isLt
      have htk := t_ge m s (s - 1)
      have htl : tl m s = t m s (s - 1) := rfl
      exact contrib_other_band x z (j := j) (k := s - 1) (fun heq => hj heq.symm) hp1 hp2
        (by rw [htl]; omega) (by rw [htl]; omega)
  rw [hrows, hhelp, hreset]
  exact congrArg (HAdd.hAdd _) hpad

end

end L90

end Jones1980
