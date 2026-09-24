import Diophantine.Paper1980.Isolation93

/-!
# Coefficient isolation, part 2: the window of a target

For the layout of `Layout93.lean` and the polynomials of `Isolation93.lean`,
this file computes the coefficients `a_p = [X^p](D · C²)` at the eight
positions `t_j − 5, …, t_j + 2` of the window of target `j`:

* the dummy digits do not reach any tested position (`coeff_eq_main`);
* only the band of target `j` contributes (`coeff_band_only`);
* within the band, the residue classes modulo six of the exponents give the
  values listed in `Isolation93.lean` (`a_t`, `a_reset`, `a_pad`, `a_zero`).
-/

namespace Jones1980

namespace Iso

open Polynomial Layout

noncomputable section

/-- The contribution of the monomial `c X^e` to the coefficient of `X^p` in `c X^e · Q`. -/
def contrib (c : ℤ) (e p : ℕ) (Q : ℤ[X]) : ℤ := if e ≤ p then c * Q.coeff (p - e) else 0

theorem coeff_monomial_mul (c : ℤ) (e : ℕ) (Q : ℤ[X]) (p : ℕ) :
    (C c * X ^ e * Q).coeff p = contrib c e p Q := coeff_C_mul_X_pow_mul c e Q p

theorem coeff_X_pow_mul_eq (e : ℕ) (Q : ℤ[X]) (p : ℕ) :
    (X ^ e * Q).coeff p = contrib 1 e p Q := by
  rw [← coeff_monomial_mul, C_1, one_mul]

/-- A product has zero coefficient below the sum of the vanishing thresholds. -/
theorem coeff_mul_eq_zero_of_lt {P Q : ℤ[X]} {A B n : ℕ}
    (hP : ∀ i, i < A → P.coeff i = 0) (hQ : ∀ j, j < B → Q.coeff j = 0) (hn : n < A + B) :
    (P * Q).coeff n = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : ij.1 < A
  · rw [hP _ hi, zero_mul]
  · rw [hQ _ (by omega), mul_zero]

section Window

variable {m s : ℕ} (rows : Fin s → Row m) (P5 P7 : Finset (Fin m)) (x : ℤ) (z : Fin m → ℤ)
  (dum : Fin s → Fin 3 → ℤ)

/-- `[X^p] (D · (C_main + C_dum)²) = [X^p] (D · C_main²)` for every tested position
`p ≤ t_{s−1} + 2`. -/
theorem coeff_eq_main (hs : 1 ≤ s) (p : ℕ) (hp : p ≤ t m s (s - 1) + 2) :
    (D m s rows P5 P7 * (Cmain m x z + Cdum m s dum) ^ 2).coeff p =
      (D m s rows P5 P7 * Cmain m x z ^ 2).coeff p := by
  have hexp : (Cmain m x z + Cdum m s dum) ^ 2 =
      Cmain m x z ^ 2 + (2 * Cmain m x z + Cdum m s dum) * Cdum m s dum := by ring
  rw [hexp, mul_add, coeff_add]
  have hD : ∀ i, i < t m s 0 - 2 * M m → (D m s rows P5 P7).coeff i = 0 := by
    intro i hi
    unfold D
    rw [coeff_add, coeff_add, coeff_add, finsetSum_coeff, finsetSum_coeff]
    have hM := M_pos m
    have hM6 : 6 ≤ M m := by
      unfold M; have := Nat.one_le_pow (m - 1) 3 (by norm_num); omega
    have ht0 := t_zero_gt m s
    have hd0 := d0_gt m
    have hrow : ∀ j : Fin s, (rowPoly m s j (rows j)).coeff i = 0 := by
      intro j
      unfold rowPoly
      rw [coeff_list_sum]
      apply List.sum_eq_zero
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      rw [coeff_C_mul_X_pow]
      have hw := (Row.terms_weight (rows j) q hq).2
      have : t m s 0 ≤ t m s j := by
        rcases Nat.eq_zero_or_pos j.1 with h0 | h0
        · rw [show (j : ℕ) = 0 from h0]
        · have := t_sub_ge (m := m) (s := s) h0; omega
      split_ifs with h
      · exfalso; unfold M at hi hw; omega
      · rfl
    have hreset : ∀ j : Fin s, (resetPoly m s j).coeff i = 0 := by
      intro j
      unfold resetPoly
      rw [coeff_X_pow]
      have : t m s 0 ≤ t m s j := by
        rcases Nat.eq_zero_or_pos j.1 with h0 | h0
        · rw [show (j : ℕ) = 0 from h0]
        · have := t_sub_ge (m := m) (s := s) h0; omega
      split_ifs with h
      · exfalso; omega
      · rfl
    have hpad : ∀ (j : ℕ) (P : Finset (Fin m)), (padPoly m s j P).coeff i = 0 := by
      intro j P
      unfold padPoly
      rw [coeff_add, coeff_X_pow, finsetSum_coeff]
      have hj : t m s 0 ≤ t m s j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0]
        · have := t_sub_ge (m := m) (s := s) h0; omega
      rw [Finset.sum_eq_zero]
      · split_ifs with h
        · exfalso; omega
        · rfl
      · intro q _
        rw [coeff_X_pow]
        have := v_le_M q.2
        split_ifs with h
        · exfalso; omega
        · rfl
    rw [Finset.sum_eq_zero (fun j _ => hrow j), Finset.sum_eq_zero (fun j _ => hreset j),
      hpad, hpad]
    ring
  have hC : ∀ j, j < t m s 0 → ((2 * Cmain m x z + Cdum m s dum) * Cdum m s dum).coeff j = 0 := by
    intro j hj
    have hdum : ∀ i, i < t m s 0 → (Cdum m s dum).coeff i = 0 := by
      intro i hi
      unfold Cdum
      rw [finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro k _
      rw [finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro e _
      rw [coeff_C_mul_X_pow]
      have : t m s 0 ≤ t m s k := by
        rcases Nat.eq_zero_or_pos k.1 with h0 | h0
        · rw [show (k : ℕ) = 0 from h0]
        · have := t_sub_ge (m := m) (s := s) h0; omega
      split_ifs with h
      · exfalso; omega
      · rfl
    exact coeff_mul_eq_zero_of_lt (A := 0) (B := t m s 0) (fun i hi => by omega) hdum (by omega)
  have hzero : (D m s rows P5 P7 * ((2 * Cmain m x z + Cdum m s dum) * Cdum m s dum)).coeff p = 0 := by
    apply coeff_mul_eq_zero_of_lt hD hC
    have := dummy_exclusion (m := m) (s := s) (u := t m s 0) (d := t m s 0 - 2 * M m) hs le_rfl
      (by omega)
    omega
  rw [hzero, add_zero]

end Window

end

end Iso

end Jones1980
