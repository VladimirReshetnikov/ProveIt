import Diophantine.Paper1980.Isolation93c

/-!
# Coefficient isolation, part 4: the eight positions of a window

With `coeff_band_only`, the value of `[X^p](D · C_main²)` at each position
of the window of target `j` is computed from the residue classes modulo six:
the main exponents `t_j − w` are `≡ 0`, the reset `t_j − 3` is `≡ 3`, the
paddings `t_j − 1 − v_q` are `≡ 5`, and `C_main²` has coefficients only at
multiples of six.
-/

namespace Jones1980

namespace Iso

open Polynomial Layout

noncomputable section

section Values

variable {m s : ℕ} (rows : Fin s → Row m) (P5 P7 : Finset (Fin m)) (x : ℤ) (z : Fin m → ℤ)

/-- A main exponent `t_j − w` (`6 ∣ w ≤ t_j`) contributes nothing at `p` unless `6 ∣ p`. -/
theorem contrib_main_zero {j w p : ℕ} {cz : ℤ} (hw6 : 6 ∣ w) (hwt : w ≤ t m s j)
    (hp : ¬ 6 ∣ p) : contrib cz (t m s j - w) p (Cmain m x z ^ 2) = 0 := by
  apply contrib_eq_zero x z
  rintro ⟨hep, hdvd, -⟩
  have h6 : 6 ∣ t m s j - w := Nat.dvd_sub (six_dvd_t m s j) hw6
  have : p = (p - (t m s j - w)) + (t m s j - w) := by omega
  exact hp (this ▸ dvd_add hdvd h6)

/-- The reset exponent `t_j − 3` contributes nothing at `p` unless `p % 6 = 3`. -/
theorem contrib_reset_zero {j p : ℕ} {cz : ℤ} (hj : 3 ≤ t m s j) (hp : p % 6 ≠ 3) :
    contrib cz (t m s j - 3) p (Cmain m x z ^ 2) = 0 := by
  apply contrib_eq_zero x z
  rintro ⟨hep, hdvd, -⟩
  have h6 := six_dvd_t m s j
  omega

/-- A padding exponent `t_j − 1 − u` (`6 ∣ u`, `u + 1 ≤ t_j`) contributes nothing at `p`
unless `p % 6 = 5`. -/
theorem contrib_pad_zero {j u p : ℕ} {cz : ℤ} (hu6 : 6 ∣ u) (hut : u + 1 ≤ t m s j)
    (hp : p % 6 ≠ 5) : contrib cz (t m s j - 1 - u) p (Cmain m x z ^ 2) = 0 := by
  apply contrib_eq_zero x z
  rintro ⟨hep, hdvd, -⟩
  have h6 := six_dvd_t m s j
  omega

/-- The sum of a row's contributions at its own target is the row's value. -/
theorem row_terms_at_target (j : ℕ) (R : Row m) (hcross : ∀ q ∈ R.cross, q.1 ≠ q.2.1)
    (hM : 2 * M m ≤ t m s j) :
    (R.terms.map fun q => contrib q.2 (t m s j - q.1) (t m s j) (Cmain m x z ^ 2)).sum =
      R.val x z := by
  have key : ∀ q ∈ R.terms,
      contrib q.2 (t m s j - q.1) (t m s j) (Cmain m x z ^ 2) = q.2 * (Cmain m x z ^ 2).coeff q.1 := by
    intro q hq
    have hw := (Row.terms_weight R q hq).2
    unfold contrib
    rw [if_pos (by omega), Nat.sub_sub_self (by unfold M at hM; omega)]
  rw [List.map_congr_left key]
  unfold Row.terms Row.val
  simp only [List.map_append, List.map_map, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Function.comp_def]
  rw [coeff_Cmain_sq_zero]
  have e1 : (R.sq.map fun q => q.2 * (Cmain m x z ^ 2).coeff (2 * v q.1)) =
      R.sq.map fun q => q.2 * z q.1 ^ 2 :=
    List.map_congr_left (fun q _ => by rw [coeff_Cmain_sq_two_v])
  have e2 : (R.cross.map fun q => q.2.2 * (Cmain m x z ^ 2).coeff (v q.1 + v q.2.1)) =
      R.cross.map fun q => 2 * q.2.2 * z q.1 * z q.2.1 :=
    List.map_congr_left (fun q hq => by rw [coeff_Cmain_sq_add_v x z (hcross q hq)]; ring)
  have e3 : (R.xz.map fun q => q.2 * (Cmain m x z ^ 2).coeff (v q.1)) =
      R.xz.map fun q => 2 * q.2 * x * z q.1 :=
    List.map_congr_left (fun q _ => by rw [coeff_Cmain_sq_v]; ring)
  rw [e1, e2, e3]; ring

variable (hs : 3 ≤ s) (j : Fin s)

include hs

omit hs in
theorem t_ge_M (j : Fin s) : 2 * M m + 6 ≤ t m s j := by
  have := t_zero_gt m s
  have hd : d0 m = 4 * M m + 6 := rfl
  have : t m s 0 ≤ t m s j := by
    rcases Nat.eq_zero_or_pos j.1 with h0 | h0
    · rw [show (j : ℕ) = 0 from h0]
    · have := t_sub_ge (m := m) (s := s) h0; omega
  omega

/-- The value at the target position `t_j` is the value of row `j`. -/
theorem coeff_at_target (hcross : ∀ q ∈ (rows j).cross, q.1 ≠ q.2.1) :
    (D m s rows P5 P7 * Cmain m x z ^ 2).coeff (t m s j) = (rows j).val x z := by
  have hM := M_pos m
  have hMj := t_ge_M (m := m) (s := s) j
  rw [coeff_band_only rows P5 P7 x z hs j (t m s j) (by omega) (by omega)]
  rw [row_terms_at_target x z j (rows j) hcross (by omega)]
  have h6 := six_dvd_t m s j
  rw [contrib_reset_zero x z (by omega) (by omega)]
  have hpad : ∀ (k : ℕ) (P : Finset (Fin m)), k < s → (j : ℕ) = k →
      contrib 1 (t m s k - 1) (t m s j) (Cmain m x z ^ 2) +
        ∑ q ∈ P, contrib 1 (t m s k - 1 - v q) (t m s j) (Cmain m x z ^ 2) = 0 := by
    intro k P hk hjk
    rw [hjk] at h6 hMj ⊢
    have h1 : contrib 1 (t m s k - 1) (t m s k) (Cmain m x z ^ 2) = 0 := by
      have := contrib_pad_zero x z (m := m) (s := s) (j := k) (u := 0) (p := t m s k) (cz := 1)
        (dvd_zero 6) (by omega) (by omega)
      simpa using this
    rw [h1, Finset.sum_eq_zero]
    · simp
    · intro q _
      exact contrib_pad_zero x z (six_dvd_v q) (by have := v_le_M q.2; omega) (by omega)
  split_ifs with h2 h3 h3
  · rw [hpad _ _ (by omega) h2, hpad _ _ (by omega) h3]; ring
  · rw [hpad _ _ (by omega) h2]; ring
  · rw [hpad _ _ (by omega) h3]; ring
  · ring

/-- The value at the reset position `t_j − 3` is `x²`. -/
theorem coeff_at_reset :
    (D m s rows P5 P7 * Cmain m x z ^ 2).coeff (t m s j - 3) = x ^ 2 := by
  have hM := M_pos m
  have hMj := t_ge_M (m := m) (s := s) j
  have h6 := six_dvd_t m s j
  rw [coeff_band_only rows P5 P7 x z hs j (t m s j - 3) (by omega) (by omega)]
  have hmain : ((rows j).terms.map fun q =>
      contrib q.2 (t m s j - q.1) (t m s j - 3) (Cmain m x z ^ 2)).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hw := Row.terms_weight (rows j) q hq
    exact contrib_main_zero x z hw.1 (by unfold M at hMj; omega) (by omega)
  have hreset : contrib 1 (t m s j - 3) (t m s j - 3) (Cmain m x z ^ 2) = x ^ 2 := by
    unfold contrib
    rw [if_pos le_rfl, Nat.sub_self, coeff_Cmain_sq_zero, one_mul]
  have hpad : ∀ (k : ℕ) (P : Finset (Fin m)), (j : ℕ) = k →
      contrib 1 (t m s k - 1) (t m s j - 3) (Cmain m x z ^ 2) +
        ∑ q ∈ P, contrib 1 (t m s k - 1 - v q) (t m s j - 3) (Cmain m x z ^ 2) = 0 := by
    intro k P hjk
    subst hjk
    have h1 : contrib 1 (t m s j - 1) (t m s j - 3) (Cmain m x z ^ 2) = 0 := by
      have := contrib_pad_zero x z (m := m) (s := s) (j := j) (u := 0) (p := t m s j - 3) (cz := 1)
        (dvd_zero 6) (by omega) (by omega)
      simpa using this
    rw [h1, Finset.sum_eq_zero]
    · simp
    · intro q _
      exact contrib_pad_zero x z (six_dvd_v q) (by have := v_le_M q.2; omega) (by omega)
  rw [hmain, hreset]
  split_ifs with h2 h3 h3
  · rw [hpad _ _ h2, hpad _ _ h3]; ring
  · rw [hpad _ _ h2]; ring
  · rw [hpad _ _ h3]; ring
  · ring

/-- The value at `t_j − 1`: the padding of `j`, if any. -/
theorem coeff_at_pad :
    (D m s rows P5 P7 * Cmain m x z ^ 2).coeff (t m s j - 1) =
      (if (j : ℕ) = s - 2 then x ^ 2 + ∑ q ∈ P5, 2 * x * z q else 0) +
      (if (j : ℕ) = s - 1 then x ^ 2 + ∑ q ∈ P7, 2 * x * z q else 0) := by
  have hM := M_pos m
  have hMj := t_ge_M (m := m) (s := s) j
  have h6 := six_dvd_t m s j
  rw [coeff_band_only rows P5 P7 x z hs j (t m s j - 1) (by omega) (by omega)]
  have hmain : ((rows j).terms.map fun q =>
      contrib q.2 (t m s j - q.1) (t m s j - 1) (Cmain m x z ^ 2)).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hw := Row.terms_weight (rows j) q hq
    exact contrib_main_zero x z hw.1 (by unfold M at hMj; omega) (by omega)
  rw [hmain, contrib_reset_zero x z (by omega) (by omega)]
  have hpad : ∀ (k : ℕ) (P : Finset (Fin m)), (j : ℕ) = k →
      contrib 1 (t m s k - 1) (t m s j - 1) (Cmain m x z ^ 2) +
        ∑ q ∈ P, contrib 1 (t m s k - 1 - v q) (t m s j - 1) (Cmain m x z ^ 2) =
        x ^ 2 + ∑ q ∈ P, 2 * x * z q := by
    intro k P hjk
    subst hjk
    have h1 : contrib 1 (t m s j - 1) (t m s j - 1) (Cmain m x z ^ 2) = x ^ 2 := by
      unfold contrib
      rw [if_pos le_rfl, Nat.sub_self, coeff_Cmain_sq_zero, one_mul]
    rw [h1]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    have hv := v_le_M q.2
    unfold contrib
    rw [if_pos (by omega), show t m s j - 1 - (t m s j - 1 - v q) = v q by omega,
      coeff_Cmain_sq_v, one_mul]
  split_ifs with h2 h3 h3
  · rw [hpad _ _ h2, hpad _ _ h3]; ring
  · rw [hpad _ _ h2]; ring
  · rw [hpad _ _ h3]; ring
  · ring

/-- The value at a position `p` of the window with `p % 6 ∉ {0, 3, 5}` is `0`. -/
theorem coeff_at_empty (p : ℕ) (hp1 : t m s j ≤ p + 5) (hp2 : p ≤ t m s j + 2)
    (h0 : ¬ 6 ∣ p) (h3 : p % 6 ≠ 3) (h5 : p % 6 ≠ 5) :
    (D m s rows P5 P7 * Cmain m x z ^ 2).coeff p = 0 := by
  have hM := M_pos m
  have hMj := t_ge_M (m := m) (s := s) j
  rw [coeff_band_only rows P5 P7 x z hs j p hp1 hp2]
  have hmain : ((rows j).terms.map fun q =>
      contrib q.2 (t m s j - q.1) p (Cmain m x z ^ 2)).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hw := Row.terms_weight (rows j) q hq
    exact contrib_main_zero x z hw.1 (by unfold M at hMj; omega) h0
  rw [hmain, contrib_reset_zero x z (by omega) h3]
  have hpad : ∀ (k : ℕ) (P : Finset (Fin m)), (j : ℕ) = k →
      contrib 1 (t m s k - 1) p (Cmain m x z ^ 2) +
        ∑ q ∈ P, contrib 1 (t m s k - 1 - v q) p (Cmain m x z ^ 2) = 0 := by
    intro k P hjk
    subst hjk
    have h1 : contrib 1 (t m s j - 1) p (Cmain m x z ^ 2) = 0 := by
      have := contrib_pad_zero x z (m := m) (s := s) (j := j) (u := 0) (p := p) (cz := 1)
        (dvd_zero 6) (by omega) h5
      simpa using this
    rw [h1, Finset.sum_eq_zero]
    · simp
    · intro q _
      exact contrib_pad_zero x z (six_dvd_v q) (by have := v_le_M q.2; omega) h5
  split_ifs with h2 h3' h3'
  · rw [hpad _ _ h2, hpad _ _ h3']; ring
  · rw [hpad _ _ h2]; ring
  · rw [hpad _ _ h3']; ring
  · ring

end Values

end

end Iso

end Jones1980
