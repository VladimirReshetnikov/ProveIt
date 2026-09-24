import Diophantine.Paper1980.Index93

/-!
# The coefficients of `D` lie in `{−1, 0, 1}` (Section 2)

For a layout whose rows are *valid* — signs `±1`, pairwise distinct monomial
weights, cross pairs of distinct coordinates — every coefficient of
`D = D_main + D_reset + D₅ + D₇` has absolute value at most one: the three
kinds of exponents lie in different residue classes modulo six, distinct
targets occupy disjoint bands, and within one band the exponents of one
kind are distinct.  Every exponent of `D` is below `K = t_{s−1} + 3`.
-/

namespace Jones1980

namespace Iso

open Polynomial Layout

noncomputable section

/-- A valid row: signs of absolute value one, pairwise distinct monomial weights, and cross
pairs of distinct coordinates. -/
structure RowValid {m : ℕ} (R : Row m) : Prop where
  signs : ∀ p ∈ R.terms, |p.2| ≤ 1
  nodup : (R.terms.map Prod.fst).Nodup
  cross : ∀ q ∈ R.cross, q.1 ≠ q.2.1

/-- A sum of signs selected by a key that occurs at most once has absolute value `≤ 1`. -/
theorem abs_sum_ite_le_one (l : List (ℕ × ℤ)) (f : ℕ × ℤ → ℕ) (hnd : (l.map f).Nodup)
    (hsign : ∀ p ∈ l, |p.2| ≤ 1) (c : ℕ) :
    |(l.map fun p => if c = f p then p.2 else 0).sum| ≤ 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hp : c = f p
    · rw [if_pos hp]
      have h0 : (l.map fun q => if c = f q then q.2 else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨q, hq, rfl⟩ := hy
        have : c ≠ f q := fun h => hnd.1 (List.mem_map.2 ⟨q, hq, by rw [← h, hp]⟩)
        rw [if_neg this]
      rw [h0, add_zero]; exact hsign p (by simp)
    · rw [if_neg hp, zero_add]
      exact ih hnd.2 (fun q hq => hsign q (by simp [hq]))

/-- A finite sum of terms of absolute value `≤ 1`, at most one of which is nonzero, has
absolute value `≤ 1`. -/
theorem abs_sum_le_one_of_unique {ι : Type*} [Fintype ι] (f : ι → ℤ) (h1 : ∀ j, |f j| ≤ 1)
    (hu : ∀ j k, f j ≠ 0 → f k ≠ 0 → j = k) : |∑ j, f j| ≤ 1 := by
  by_cases hex : ∃ j, f j ≠ 0
  · obtain ⟨j, hj⟩ := hex
    rw [Finset.sum_eq_single j (fun k _ hk => by_contra fun h => hk (hu k j h hj)) (by simp)]
    exact h1 j
  · push Not at hex
    simp [hex]

section Coeffs

variable {m s : ℕ}

theorem t_ge_two_M (m s j : ℕ) : 2 * M m + 6 ≤ t m s j := by
  unfold t d0; have := M_pos m; nlinarith

theorem t_mono {j k : ℕ} (hjk : j ≤ k) : t m s j ≤ t m s k := by
  rcases Nat.eq_or_lt_of_le hjk with rfl | h
  · exact le_rfl
  · have := t_sub_ge (m := m) (s := s) h; omega

theorem t_inj {j k : ℕ} (h : t m s j = t m s k) : j = k := by
  by_contra hne
  have hd0 := d0_gt m
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := t_sub_ge (m := m) (s := s) hlt; omega
  · have := t_sub_ge (m := m) (s := s) hgt; omega

/-- Two targets whose bands `[t − 2M, t]` both contain `h` coincide. -/
theorem band_eq_of_mem {j k h : ℕ} (hj1 : t m s j ≤ h + 2 * M m) (hj2 : h ≤ t m s j)
    (hk1 : t m s k ≤ h + 2 * M m) (hk2 : h ≤ t m s k) : j = k := by
  by_contra hne
  have hd0 := d0_gt m
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := t_sub_ge (m := m) (s := s) hlt; omega
  · have := t_sub_ge (m := m) (s := s) hgt; omega

theorem coeff_rowPoly (j : ℕ) (R : Row m) (h : ℕ) :
    (rowPoly m s j R).coeff h =
      (R.terms.map fun p => if h = t m s j - p.1 then p.2 else 0).sum := by
  unfold rowPoly
  rw [coeff_list_sum]
  congr 1
  exact List.map_congr_left fun p _ => by rw [coeff_C_mul_X_pow]

theorem abs_coeff_rowPoly_le (j : ℕ) (R : Row m) (hR : RowValid R) (h : ℕ) :
    |(rowPoly m s j R).coeff h| ≤ 1 := by
  have hM := t_ge_two_M m s j
  rw [coeff_rowPoly]
  apply abs_sum_ite_le_one _ (fun p => t m s j - p.1) _ hR.signs
  rw [show (fun p : ℕ × ℤ => t m s j - p.1) = (fun w => t m s j - w) ∘ Prod.fst from rfl,
    ← List.map_map]
  apply List.Nodup.map_on _ hR.nodup
  intro x hx y hy hxy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
  have := (Row.terms_weight R p hp).2
  have := (Row.terms_weight R q hq).2
  unfold M at hM
  omega

theorem coeff_rowPoly_ne_zero (j : ℕ) (R : Row m) (h : ℕ)
    (hne : (rowPoly m s j R).coeff h ≠ 0) :
    6 ∣ h ∧ t m s j ≤ h + 2 * M m ∧ h ≤ t m s j := by
  have hM := t_ge_two_M m s j
  rw [coeff_rowPoly] at hne
  obtain ⟨p, hp, hph⟩ : ∃ p ∈ R.terms, h = t m s j - p.1 := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [if_neg (hcon p hp)]
  have hw := Row.terms_weight R p hp
  have h6 := six_dvd_t m s j
  unfold M at hM ⊢
  refine ⟨?_, by omega, by omega⟩
  rw [hph]
  exact Nat.dvd_sub h6 hw.1

theorem coeff_resetPoly (j h : ℕ) :
    (resetPoly m s j).coeff h = if h = t m s j - 3 then 1 else 0 := by
  unfold resetPoly; rw [coeff_X_pow]

theorem coeff_padPoly (j : ℕ) (P : Finset (Fin m)) (h : ℕ) :
    (padPoly m s j P).coeff h =
      (if h = t m s j - 1 then 1 else 0) + ∑ p ∈ P, if h = t m s j - 1 - v p then 1 else 0 := by
  unfold padPoly
  rw [coeff_add, coeff_X_pow, finsetSum_coeff]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by rw [coeff_X_pow]

theorem coeff_padPoly_bounds (j : ℕ) (P : Finset (Fin m)) (h : ℕ) :
    0 ≤ (padPoly m s j P).coeff h ∧ (padPoly m s j P).coeff h ≤ 1 := by
  have hM := t_ge_two_M m s j
  rw [coeff_padPoly]
  by_cases h1 : h = t m s j - 1
  · rw [if_pos h1]
    have : ∑ p ∈ P, (if h = t m s j - 1 - v p then (1 : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro p _
      rw [if_neg]; have := v_pos p; have := v_le_M p.2; omega
    rw [this]; norm_num
  · rw [if_neg h1, zero_add]
    constructor
    · exact Finset.sum_nonneg fun p _ => by split_ifs <;> norm_num
    · by_cases hex : ∃ p ∈ P, h = t m s j - 1 - v p
      · obtain ⟨p, hp, hph⟩ := hex
        rw [Finset.sum_eq_single p]
        · rw [if_pos hph]
        · intro q hq hqp
          rw [if_neg]
          intro hqh
          apply hqp
          have hvp := v_le_M p.2; have hvq := v_le_M q.2
          have : v q = v p := by omega
          exact Fin.ext (v_strictMono.injective this)
        · intro hp'; exact absurd hp hp'
      · push Not at hex
        rw [Finset.sum_eq_zero fun p hp => by rw [if_neg (hex p hp)]]
        norm_num

theorem coeff_padPoly_ne_zero (j : ℕ) (P : Finset (Fin m)) (h : ℕ)
    (hne : (padPoly m s j P).coeff h ≠ 0) :
    h % 6 = 5 ∧ t m s j ≤ h + 1 + M m ∧ h + 1 ≤ t m s j := by
  have hM := t_ge_two_M m s j
  rw [coeff_padPoly] at hne
  have h6 := six_dvd_t m s j
  by_cases h1 : h = t m s j - 1
  · refine ⟨by omega, by omega, by omega⟩
  · rw [if_neg h1, zero_add] at hne
    obtain ⟨p, hp, hph⟩ : ∃ p ∈ P, h = t m s j - 1 - v p := by
      by_contra hcon; push Not at hcon
      exact hne (Finset.sum_eq_zero fun p hp => by rw [if_neg (hcon p hp)])
    have := v_le_M p.2; have := six_dvd_v p
    refine ⟨?_, by omega, by omega⟩
    omega

variable (rows : Fin s → Row m) (P5 P7 : Finset (Fin m))

theorem coeff_D (h : ℕ) : (D m s rows P5 P7).coeff h =
    (∑ j : Fin s, (rowPoly m s j (rows j)).coeff h) +
      (∑ j : Fin s, (resetPoly m s j).coeff h) +
      (padPoly m s (s - 2) P5).coeff h + (padPoly m s (s - 1) P7).coeff h := by
  unfold D
  rw [coeff_add, coeff_add, coeff_add, finsetSum_coeff, finsetSum_coeff]

/-- Every coefficient of `D` has absolute value at most one. -/
theorem abs_coeff_D_le_one (hs : 3 ≤ s) (hrows : ∀ j, RowValid (rows j)) (h : ℕ) :
    |(D m s rows P5 P7).coeff h| ≤ 1 := by
  rw [coeff_D]
  have hrow0 : ¬ 6 ∣ h → ∑ j : Fin s, (rowPoly m s j (rows j)).coeff h = 0 := fun h0 =>
    Finset.sum_eq_zero fun j _ => by
      by_contra hne; exact h0 (coeff_rowPoly_ne_zero j (rows j) h hne).1
  have hreset0 : h % 6 ≠ 3 → ∑ j : Fin s, (resetPoly m s j).coeff h = 0 := fun h3 =>
    Finset.sum_eq_zero fun j _ => by
      rw [coeff_resetPoly]
      have h6 := six_dvd_t m s j; have := t_ge_two_M m s j
      rw [if_neg]; omega
  have hpad0 : ∀ (k : ℕ) (P : Finset (Fin m)), h % 6 ≠ 5 → (padPoly m s k P).coeff h = 0 :=
    fun k P h5 => by
      by_contra hne; exact h5 (coeff_padPoly_ne_zero k P h hne).1
  by_cases h0 : 6 ∣ h
  · rw [hreset0 (by omega), hpad0 _ _ (by omega), hpad0 _ _ (by omega), add_zero, add_zero,
      add_zero]
    apply abs_sum_le_one_of_unique
    · intro j; exact abs_coeff_rowPoly_le j (rows j) (hrows j) h
    · intro j k hj hk
      obtain ⟨_, hj1, hj2⟩ := coeff_rowPoly_ne_zero j (rows j) h hj
      obtain ⟨_, hk1, hk2⟩ := coeff_rowPoly_ne_zero k (rows k) h hk
      exact Fin.ext (band_eq_of_mem hj1 hj2 hk1 hk2)
  · by_cases h3 : h % 6 = 3
    · rw [hrow0 h0, hpad0 _ _ (by omega), hpad0 _ _ (by omega), zero_add, add_zero, add_zero]
      apply abs_sum_le_one_of_unique
      · intro j; rw [coeff_resetPoly]; split_ifs <;> norm_num
      · intro j k hj hk
        rw [coeff_resetPoly] at hj hk
        split_ifs at hj hk with hj' hk'
        · have := t_ge_two_M m s j; have := t_ge_two_M m s k
          exact Fin.ext (t_inj (m := m) (s := s) (by omega))
        · exact absurd rfl hk
        · exact absurd rfl hj
        · exact absurd rfl hj
    · by_cases h5 : h % 6 = 5
      · rw [hrow0 h0, hreset0 h3, zero_add, zero_add]
        obtain ⟨hp5a, hp5b⟩ := coeff_padPoly_bounds (s := s) (s - 2) P5 h
        obtain ⟨hp7a, hp7b⟩ := coeff_padPoly_bounds (s := s) (s - 1) P7 h
        -- the two padding bands are disjoint
        have hnot : (padPoly m s (s - 2) P5).coeff h = 0 ∨ (padPoly m s (s - 1) P7).coeff h = 0 := by
          by_contra hcon
          push Not at hcon
          obtain ⟨_, ha1, ha2⟩ := coeff_padPoly_ne_zero (s - 2) P5 h hcon.1
          obtain ⟨_, hb1, hb2⟩ := coeff_padPoly_ne_zero (s - 1) P7 h hcon.2
          have hsucc : t m s (s - 1) = t m s (s - 2) + d0 m := by
            rw [show s - 1 = (s - 2) + 1 by omega, t_succ]
          have := d0_gt m
          omega
        rcases hnot with hz | hz
        · rw [hz, zero_add]; rw [abs_le]; constructor <;> linarith
        · rw [hz, add_zero]; rw [abs_le]; constructor <;> linarith
      · rw [hrow0 h0, hreset0 h3, hpad0 _ _ h5, hpad0 _ _ h5]
        norm_num

/-- Every exponent of `D` is below `K = t_{s−1} + 3`. -/
theorem coeff_D_eq_zero_of_ge (hs : 1 ≤ s) (h : ℕ) (hK : K m s ≤ h) :
    (D m s rows P5 P7).coeff h = 0 := by
  rw [coeff_D]
  have hlast : ∀ j : Fin s, t m s j ≤ t m s (s - 1) := fun j => t_mono (by omega)
  unfold K at hK
  have h1 : ∑ j : Fin s, (rowPoly m s j (rows j)).coeff h = 0 :=
    Finset.sum_eq_zero fun j _ => by
      by_contra hne
      have := (coeff_rowPoly_ne_zero j (rows j) h hne).2.2
      have := hlast j; omega
  have h2 : ∑ j : Fin s, (resetPoly m s j).coeff h = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [coeff_resetPoly, if_neg]; have := hlast j; omega
  have h3 : ∀ (k : ℕ) (P : Finset (Fin m)), k ≤ s - 1 → (padPoly m s k P).coeff h = 0 :=
    fun k P hk => by
      by_contra hne
      have := (coeff_padPoly_ne_zero k P h hne).2.2
      have := t_mono (m := m) (s := s) hk; omega
  rw [h1, h2, h3 _ _ (by omega), h3 _ _ le_rfl]; rfl

end Coeffs

end

end Iso

end Jones1980
