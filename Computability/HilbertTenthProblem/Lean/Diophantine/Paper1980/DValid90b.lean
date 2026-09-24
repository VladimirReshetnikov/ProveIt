import Diophantine.Paper1980.DValid90

/-!
# The coefficients of `D` for the 90-operation layout, part 2

Every nonzero coefficient of `D` is `±1` (`abs_coeff_D_le_one`); the negative
coefficients sit at tested starts (`coeff_D_neg_mem_Rset`), the positive ones
are off the indicator support (`coeff_D_nonpos_of_mem_supp`); the support of
`D` lies below `K` (`coeff_D_eq_zero_of_ge`); the leading term is the last
reset `X^(t_last − 4)` (`coeff_D_tl_sub_four`, `coeff_D_eq_zero_of_gt`), so
`D(B) > 0` for every `B ≥ 2` (`D_eval_pos`).
-/

namespace Jones1980

namespace L90

open Polynomial Finset
open Layout (Row)

noncomputable section

variable {m s : ℕ} (rows : Fin s → Row m) (hel : Fin s → Fin 3 → Fin m) (PX : Finset (Fin m))

/-- The indicator support: the coordinate weights and the three positions of every start. -/
def supp : Finset ℕ :=
  (Finset.univ.image fun i : Fin m => v (i : ℕ)) ∪
    (Rset s rows).biUnion fun r => {r, r + 1, r + 2}

theorem mem_supp {h : ℕ} : h ∈ supp rows ↔
    (∃ i : Fin m, h = v i) ∨ ∃ r ∈ Rset s rows, h = r ∨ h = r + 1 ∨ h = r + 2 := by
  unfold supp
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨i, hi⟩ | ⟨r, hr, hh⟩)
    · exact Or.inl ⟨i, hi.symm⟩
    · exact Or.inr ⟨r, hr, hh⟩
  · rintro (⟨i, hi⟩ | ⟨r, hr, hh⟩)
    · exact Or.inl ⟨i, hi.symm⟩
    · exact Or.inr ⟨r, hr, hh⟩

theorem mem_supp_of_mem_Rset {r : ℕ} (hr : r ∈ Rset s rows) : r ∈ supp rows :=
  (mem_supp rows).2 (Or.inr ⟨r, hr, Or.inl rfl⟩)

theorem mem_supp_of_mem_Rset_add {r e : ℕ} (hr : r ∈ Rset s rows) (he : e < 3) :
    r + e ∈ supp rows := by
  apply (mem_supp rows).2
  right; refine ⟨r, hr, ?_⟩
  interval_cases e <;> simp

theorem v_mem_supp (i : Fin m) : v i ∈ supp rows := (mem_supp rows).2 (Or.inl ⟨i, rfl⟩)

/-- A position of `supp` that is divisible by eight and exceeds `M` is a start. -/
theorem mem_Rset_of_mem_supp {h : ℕ} (hh : h ∈ supp rows) (h8 : 8 ∣ h) (hM : M m < h) :
    h ∈ Rset s rows := by
  rcases (mem_supp rows).1 hh with ⟨i, hi⟩ | ⟨r, hr, hr'⟩
  · exfalso; have := v_le_M i.isLt; omega
  · obtain ⟨j, hj⟩ := (mem_Rset s rows).1 hr
    have := eight_dvd_of_mem_starts rows hj
    rcases hr' with rfl | rfl | rfl
    · exact hr
    · omega
    · omega

/-- Two bands meeting at one position coincide. -/
theorem band_of_two {j k : Fin s} {h : ℕ} (hj1 : t m s j ≤ h + 4 * M m) (hj2 : h ≤ t m s j)
    (hk1 : t m s k ≤ h + 4 * M m) (hk2 : h ≤ t m s k) : j = k := by
  by_contra hne
  have hd0 := d0_gt m
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · have := t_sub_ge (m := m) (s := s) hlt; omega
  · have := t_sub_ge (m := m) (s := s) hgt; omega

variable (hL : LayoutOk s rows hel)
include hL

theorem rows_sum_cases (h : ℕ) :
    (∑ j : Fin s, (rowPoly s j (rows j)).coeff h) = 0 ∨
      ∃ j : Fin s, (rowPoly s j (rows j)).coeff h ≠ 0 ∧
        (∑ j : Fin s, (rowPoly s j (rows j)).coeff h) = (rowPoly s j (rows j)).coeff h :=
  sum_unique _ fun j k hj hk => by
    have hj' := coeff_rowPoly_ne_zero (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hj
    have hk' := coeff_rowPoly_ne_zero (s := s) (hL.rows_ok k) k (by have := t_ge m s k; omega) hk
    exact band_of_two (by omega) hj'.2.2 (by omega) hk'.2.2

theorem helps_sum_cases (h : ℕ) :
    (∑ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff h) = 0 ∨
      ∃ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff h ≠ 0 ∧
        (∑ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff h) =
          (helpPoly s j (rows j) (hel j)).coeff h :=
  sum_unique _ fun j k hj hk => by
    have hj' := coeff_helpPoly_ne_zero (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hj
    have hk' := coeff_helpPoly_ne_zero (s := s) (hL.rows_ok k) k (by have := t_ge m s k; omega) hk
    exact band_of_two hj'.2.1 hj'.2.2.1 hk'.2.1 hk'.2.2.1

/-- A main term and a helper complement never share an exponent. -/
theorem helpPoly_eq_zero_of_rowPoly_ne_zero {j : Fin s} {h : ℕ}
    (hne : (rowPoly s j (rows j)).coeff h ≠ 0) (k : Fin s) :
    (helpPoly s k (rows k) (hel k)).coeff h = 0 := by
  by_contra hk
  have hR := hL.rows_ok j
  have hRk := hL.rows_ok k
  have htj := t_ge m s j
  have htk := t_ge m s k
  obtain ⟨_, hj1, hj2⟩ := coeff_rowPoly_ne_zero (s := s) hR j (by omega) hne
  obtain ⟨_, hk1, hk2, μ, hμ, π, hπ, hh⟩ := coeff_helpPoly_ne_zero (s := s) hRk k (by omega) hk
  have hjk : j = k := band_of_two (by omega) hj2 hk1 hk2
  subst hjk
  rcases coeff_rowPoly_cases (s := s) hR j (by omega) h with h0 | ⟨q, hq, hh', _⟩
  · exact hne h0
  · have := W_le_two_M_of_mem_terms hq
    have := W_le_two_M_of_mem_negs hμ
    have := W_le_two_M_of_mem_pairs hπ
    have hW : W q.1 = W (μ + π) := by rw [W_add]; omega
    have hc := card_le_two_of_mem_terms hq
    have hcπ := card_of_mem_pairs hπ
    rcases card_of_mem_negs hR hμ with hcμ | hcμ
    · have heq := W_inj (by omega) (by rw [Multiset.card_add]; omega) hW
      have := congrArg Multiset.card heq
      rw [Multiset.card_add] at this; omega
    · -- a seed: its only monomial is `x²`, of weight zero
      have hxx : (rows j).xx < 0 := zero_mem_negs_iff.1 (hcμ ▸ hμ)
      rw [terms_of_seed hR hxx, List.mem_singleton] at hq
      have hq1 : q.1 = 0 := by rw [hq]
      rw [hq1, W_zero] at hW
      have := W_pos_of_ne_zero (μ := μ + π) (by
        intro h0; have := congrArg Multiset.card h0
        rw [Multiset.card_add, Multiset.card_zero] at this; omega)
      omega

/-! ### Every coefficient is `0` or `±1` -/

theorem abs_coeff_D_le_one (h : ℕ) : |(D s rows hel PX).coeff h| ≤ 1 := by
  rw [coeff_D]
  obtain ⟨hr0, hr1⟩ := coeff_resetPoly_bounds rows h
  obtain ⟨hp0, hp1⟩ := coeff_padPoly_bounds (s := s) PX h
  by_cases h8 : 8 ∣ h
  · have hres : (resetPoly s rows).coeff h = 0 := by
      by_contra hne; have := (coeff_resetPoly_ne_zero rows hne).1; omega
    have hpad : (padPoly s PX).coeff h = 0 := by
      by_contra hne; have := (coeff_padPoly_ne_zero (s := s) PX hne).1; omega
    rw [hres, hpad, add_zero, add_zero]
    rcases rows_sum_cases rows hel hL h with h0 | ⟨j, hj, hsum⟩
    · rw [h0, zero_add]
      rcases helps_sum_cases rows hel hL h with h0' | ⟨k, _, hsum'⟩
      · rw [h0']; norm_num
      · rw [hsum']
        obtain ⟨a, b⟩ := coeff_helpPoly_bounds (s := s) (hL.rows_ok k) k (by have := t_ge m s k; omega) h
        rw [abs_le]; constructor <;> linarith
    · have : ∑ k : Fin s, (helpPoly s k (rows k) (hel k)).coeff h = 0 :=
        Finset.sum_eq_zero fun k _ => helpPoly_eq_zero_of_rowPoly_ne_zero rows hel hL hj k
      rw [this, add_zero, hsum]
      exact abs_coeff_rowPoly_le (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) h
  · have hrows : ∑ j : Fin s, (rowPoly s j (rows j)).coeff h = 0 :=
      Finset.sum_eq_zero fun j _ => by
        by_contra hne
        exact h8 (coeff_rowPoly_ne_zero (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hne).1
    have hhelps : ∑ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff h = 0 :=
      Finset.sum_eq_zero fun j _ => by
        by_contra hne
        exact h8 (coeff_helpPoly_ne_zero (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hne).1
    rw [hrows, hhelps, zero_add, zero_add]
    by_cases hres : (resetPoly s rows).coeff h = 0
    · rw [hres, zero_add, abs_le]; constructor <;> linarith
    · have h4 := (coeff_resetPoly_ne_zero rows hres).1
      have hpad : (padPoly s PX).coeff h = 0 := by
        by_contra hne; have := (coeff_padPoly_ne_zero (s := s) PX hne).1; omega
      rw [hpad, add_zero, abs_le]; constructor <;> linarith

/-! ### Signs -/

theorem coeff_D_neg_mem_Rset {h : ℕ} (hneg : (D s rows hel PX).coeff h < 0) :
    h ∈ Rset s rows := by
  rw [coeff_D] at hneg
  obtain ⟨hr0, _⟩ := coeff_resetPoly_bounds rows h
  obtain ⟨hp0, _⟩ := coeff_padPoly_bounds (s := s) PX h
  have hh0 : 0 ≤ ∑ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff h :=
    Finset.sum_nonneg fun j _ =>
      (coeff_helpPoly_bounds (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) h).1
  have hrows : ∑ j : Fin s, (rowPoly s j (rows j)).coeff h < 0 := by linarith
  rcases rows_sum_cases rows hel hL h with h0 | ⟨j, _, hsum⟩
  · omega
  · rw [hsum] at hrows
    obtain ⟨μ, hμ, hh⟩ := coeff_rowPoly_neg (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hrows
    exact (mem_Rset s rows).2 ⟨j, (mem_starts s rows).2 (Or.inr ⟨μ, hμ, hh⟩)⟩

/-- A positive main term is not at a start. -/
theorem main_pos_not_mem_Rset (j : Fin s) {q : Multiset (Fin m) × ℤ} (hq : q ∈ terms (rows j))
    (hqpos : 0 < q.2) (hr : t m s j - W q.1 ∈ Rset s rows) : False := by
  have hR := hL.rows_ok j
  have htj := t_ge m s j
  have hw := W_le_two_M_of_mem_terms hq
  obtain ⟨k, hk⟩ := (mem_Rset s rows).1 hr
  obtain ⟨hb1, hb2⟩ := starts_bounds rows hk
  have hjk : j = k := band_of_two (by omega) (by omega) (by omega) hb2
  subst hjk
  rcases (mem_starts s rows).1 hk with heq | ⟨μ', hμ', heq⟩
  · have hW0 : W q.1 = 0 := by omega
    have hq0 : q.1 = 0 := by
      by_contra hne; have := W_pos_of_ne_zero hne; omega
    have : q = (q.1, q.2) := rfl
    rw [this, hq0] at hq
    have := zero_mem_terms_iff.1 hq
    have := hR.xx
    omega
  · have hw' := W_le_two_M_of_mem_negs hμ'
    have hW : W q.1 = W μ' := by omega
    have hc := card_le_two_of_mem_terms hq
    have hcμ' : Multiset.card μ' ≤ 2 := by
      rcases card_of_mem_negs hR hμ' with hc | hc
      · omega
      · rw [hc]; simp
    have heq' := W_inj (by omega) (by omega) hW
    have : q = (q.1, q.2) := rfl
    rw [this, heq'] at hq
    have := coeff_of_mem_negs hR hq hμ'
    omega

/-- A helper complement is not at a start. -/
theorem help_not_mem_Rset (k : Fin s) {μ π : Multiset (Fin m)} (hμ : μ ∈ negs (rows k))
    (hπ : π ∈ pairs (hel k)) (hr : t m s k - W μ - W π ∈ Rset s rows) : False := by
  have hR := hL.rows_ok k
  have htk := t_ge m s k
  have hwμ := W_le_two_M_of_mem_negs hμ
  have hwπ := W_le_two_M_of_mem_pairs hπ
  have hcπ := card_of_mem_pairs hπ
  obtain ⟨k', hk'⟩ := (mem_Rset s rows).1 hr
  obtain ⟨hb1, hb2⟩ := starts_bounds rows hk'
  have hkk : k = k' := band_of_two (by omega) (by omega) (by omega) hb2
  subst hkk
  have hcμ : Multiset.card μ ≤ 2 := by
    rcases card_of_mem_negs hR hμ with hc | hc
    · omega
    · rw [hc]; simp
  have hπ8 : 8 ≤ W π := W_pos_of_ne_zero (by
    intro h0; rw [h0, Multiset.card_zero] at hcπ; omega)
  rcases (mem_starts s rows).1 hk' with heq | ⟨μ₀, hμ₀, heq⟩
  · omega
  · have hw0 := W_le_two_M_of_mem_negs hμ₀
    have hcμ₀ : Multiset.card μ₀ ≤ 2 := by
      rcases card_of_mem_negs hR hμ₀ with hc | hc
      · omega
      · rw [hc]; simp
    have hW : W (μ + π) = W μ₀ := by rw [W_add]; omega
    have heq' := W_inj (by rw [Multiset.card_add]; omega) (by omega) hW
    have hcard := congrArg Multiset.card heq'
    rw [Multiset.card_add] at hcard
    rcases card_of_mem_negs hR hμ with hcμ | hcμ
    · omega
    · -- a seed: its only negative monomial is `x²`
      have hxx : (rows k).xx < 0 := zero_mem_negs_iff.1 (hcμ ▸ hμ)
      have h0 := negs_of_seed hR hxx μ₀ hμ₀
      rw [h0, Multiset.card_zero] at hcard
      omega

theorem coeff_D_nonpos_of_mem_supp {h : ℕ} (hh : h ∈ supp rows) :
    (D s rows hel PX).coeff h ≤ 0 := by
  by_contra hpos
  push Not at hpos
  rw [coeff_D] at hpos
  obtain ⟨hr0, hr1⟩ := coeff_resetPoly_bounds rows h
  obtain ⟨hp0, hp1⟩ := coeff_padPoly_bounds (s := s) PX h
  by_cases h8 : 8 ∣ h
  · have hres : (resetPoly s rows).coeff h = 0 := by
      by_contra hne; have := (coeff_resetPoly_ne_zero rows hne).1; omega
    have hpad : (padPoly s PX).coeff h = 0 := by
      by_contra hne; have := (coeff_padPoly_ne_zero (s := s) PX hne).1; omega
    rw [hres, hpad, add_zero, add_zero] at hpos
    rcases rows_sum_cases rows hel hL h with h0 | ⟨j, hj, hsum⟩
    · rw [h0, zero_add] at hpos
      rcases helps_sum_cases rows hel hL h with h0' | ⟨k, hk, hsum'⟩
      · rw [h0'] at hpos; exact lt_irrefl _ hpos
      · obtain ⟨_, hk1, hk2, μ, hμ, π, hπ, hh'⟩ :=
          coeff_helpPoly_ne_zero (s := s) (hL.rows_ok k) k (by have := t_ge m s k; omega) hk
        have htk := t_ge m s k
        have hM : M m < h := by omega
        have hr := mem_Rset_of_mem_supp rows hh h8 hM
        rw [hh'] at hr
        exact help_not_mem_Rset rows hel hL k hμ hπ hr
    · have hhelps : ∑ k : Fin s, (helpPoly s k (rows k) (hel k)).coeff h = 0 :=
        Finset.sum_eq_zero fun k _ => helpPoly_eq_zero_of_rowPoly_ne_zero rows hel hL hj k
      rw [hhelps, add_zero, hsum] at hpos
      have htj := t_ge m s j
      obtain ⟨q, hq, hqpos, hh'⟩ :=
        coeff_rowPoly_pos (s := s) (hL.rows_ok j) j (by omega) hpos
      have hw := W_le_two_M_of_mem_terms hq
      have hM : M m < h := by omega
      have hr := mem_Rset_of_mem_supp rows hh h8 hM
      rw [hh'] at hr
      exact main_pos_not_mem_Rset rows hel hL j hq hqpos hr
  · have hrows : ∑ j : Fin s, (rowPoly s j (rows j)).coeff h = 0 :=
      Finset.sum_eq_zero fun j _ => by
        by_contra hne
        exact h8 (coeff_rowPoly_ne_zero (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hne).1
    have hhelps : ∑ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff h = 0 :=
      Finset.sum_eq_zero fun j _ => by
        by_contra hne
        exact h8 (coeff_helpPoly_ne_zero (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hne).1
    rw [hrows, hhelps, zero_add, zero_add] at hpos
    -- the residues of `supp` are `0, 1, 2`, those of resets and paddings `4, 7`
    have hmod : h % 8 = 0 ∨ h % 8 = 1 ∨ h % 8 = 2 := by
      rcases (mem_supp rows).1 hh with ⟨i, hi⟩ | ⟨r, hr, hr'⟩
      · have := eight_dvd_v i; omega
      · obtain ⟨j, hj⟩ := (mem_Rset s rows).1 hr
        have := eight_dvd_of_mem_starts rows hj
        omega
    have hres : (resetPoly s rows).coeff h = 0 := by
      by_contra hne; have := (coeff_resetPoly_ne_zero rows hne).1; omega
    have hpad : (padPoly s PX).coeff h = 0 := by
      by_contra hne; have := (coeff_padPoly_ne_zero (s := s) PX hne).1; omega
    rw [hres, hpad] at hpos
    exact lt_irrefl _ hpos

/-! ### The support and the leading term -/

theorem coeff_D_eq_zero_of_gt {h : ℕ} (hh : tl m s - 4 < h) : (D s rows hel PX).coeff h = 0 := by
  have hs := hL.three_le
  have htl := t_ge m s (s - 1)
  have htl' : tl m s = t m s (s - 1) := rfl
  rw [coeff_D]
  have hrows : ∑ j : Fin s, (rowPoly s j (rows j)).coeff h = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hR := hL.rows_ok j
    have htj := t_ge m s j
    rcases coeff_rowPoly_cases (s := s) hR j (by omega) h with h0 | ⟨q, hq, hh', heq⟩
    · exact h0
    · have hw := W_le_two_M_of_mem_terms hq
      have hjl := t_le_tl (m := m) (s := s) j
      -- `h ≤ t_j ≤ t_last`, so `j` is the last row and `W q.1 < 4`, hence `q.1 = 0`
      have hj : (j : ℕ) = s - 1 := by
        by_contra hne
        have : (j : ℕ) < s - 1 := by have := j.isLt; omega
        have := t_sub_ge (m := m) (s := s) this
        have := d0_gt m
        omega
      have hW0 : W q.1 = 0 := by
        have := eight_dvd_W q.1
        omega
      have hq0 : q.1 = 0 := by
        by_contra hne; have := W_pos_of_ne_zero hne; omega
      have : q = (q.1, q.2) := rfl
      rw [this, hq0] at hq
      rw [heq, zero_mem_terms_iff.1 hq]
      exact (hL.last j hj).2
  have hhelps : ∑ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff h = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_contra hne
    obtain ⟨_, _, _, μ, hμ, π, hπ, hh'⟩ :=
      coeff_helpPoly_ne_zero (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hne
    have := W_le_two_M_of_mem_negs hμ
    have := W_pos_of_ne_zero (μ := π) (by
      intro h0; have := congrArg Multiset.card h0; rw [card_of_mem_pairs hπ] at this; simp at this)
    have := t_le_tl (m := m) (s := s) j
    omega
  have hres : (resetPoly s rows).coeff h = 0 := by
    by_contra hne
    obtain ⟨_, hmem⟩ := coeff_resetPoly_ne_zero rows hne
    have := (Rset_bounds rows hmem).2
    omega
  have hpad : (padPoly s PX).coeff h = 0 := by
    by_contra hne
    have := (coeff_padPoly_ne_zero (s := s) PX hne).2
    have := (coeff_padPoly_ne_zero (s := s) PX hne).1
    have := eight_dvd_t m s (s - 1)
    omega
  rw [hrows, hhelps, hres, hpad]; ring

theorem coeff_D_eq_zero_of_ge {h : ℕ} (hK : K m s ≤ h) : (D s rows hel PX).coeff h = 0 :=
  coeff_D_eq_zero_of_gt rows hel PX hL (by unfold K at hK; omega)

/-- The leading coefficient: the last reset. -/
theorem coeff_D_tl_sub_four : (D s rows hel PX).coeff (tl m s - 4) = 1 := by
  have hs := hL.three_le
  have htl := t_ge m s (s - 1)
  have h8 := eight_dvd_t m s (s - 1)
  have htl' : tl m s = t m s (s - 1) := rfl
  rw [coeff_D]
  have hn8 : ¬ 8 ∣ tl m s - 4 := by rw [htl']; omega
  have hrows : ∑ j : Fin s, (rowPoly s j (rows j)).coeff (tl m s - 4) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      by_contra hne
      exact hn8 (coeff_rowPoly_ne_zero (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hne).1
  have hhelps : ∑ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff (tl m s - 4) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      by_contra hne
      exact hn8 (coeff_helpPoly_ne_zero (s := s) (hL.rows_ok j) j (by have := t_ge m s j; omega) hne).1
  have hpad : (padPoly s PX).coeff (tl m s - 4) = 0 := by
    by_contra hne
    have := (coeff_padPoly_ne_zero (s := s) PX hne).1
    rw [htl'] at this; omega
  have hres : (resetPoly s rows).coeff (tl m s - 4) = 1 := by
    rw [coeff_resetPoly, if_pos]
    have : tl m s - 4 + 4 = t m s (⟨s - 1, by omega⟩ : Fin s) := by
      rw [htl']; simp only; omega
    rw [this]
    exact t_mem_Rset s rows _
  rw [hrows, hhelps, hres, hpad]; ring

omit hL in
/-- `Σ_{h<n} B^h < B^n` for `B ≥ 2`. -/
theorem geom_lt (B : ℕ) (hB : 2 ≤ B) : ∀ n : ℕ, ∑ h ∈ range n, B ^ h < B ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := geom_lt B hB n
    have : 0 < B ^ n := by positivity
    nlinarith

/-- `D(B) > 0` for `B ≥ 2`. -/
theorem D_eval_pos (B : ℤ) (hB : 2 ≤ B) : 0 < (D s rows hel PX).eval B := by
  have hs := hL.three_le
  have htl := t_ge m s (s - 1)
  have htl' : tl m s = t m s (s - 1) := rfl
  obtain ⟨N, hN⟩ : ∃ N, N = tl m s - 4 := ⟨_, rfl⟩
  have hdeg : (D s rows hel PX).natDegree < N + 1 := by
    rw [Nat.lt_succ_iff]
    apply natDegree_le_iff_coeff_eq_zero.2
    intro h hh
    exact coeff_D_eq_zero_of_gt rows hel PX hL (by omega)
  have h1 : (D s rows hel PX).coeff N = 1 := by
    rw [hN]; exact coeff_D_tl_sub_four rows hel PX hL
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, h1, one_mul]
  -- the lower part is bounded by `Σ_{h<N} B^h < B^N`
  have hB0 : (0 : ℤ) ≤ B := by linarith
  have hlow : |∑ h ∈ range N, (D s rows hel PX).coeff h * B ^ h| ≤ ∑ h ∈ range N, B ^ h := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun h _ => ?_)
    rw [abs_mul, abs_pow, abs_of_nonneg hB0]
    have := abs_coeff_D_le_one rows hel PX hL h
    have : (0 : ℤ) ≤ B ^ h := by positivity
    nlinarith
  have hgeom : ∑ h ∈ range N, B ^ h < B ^ N := by
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, (b : ℤ) = B := ⟨B.toNat, Int.toNat_of_nonneg hB0⟩
    have hb : 2 ≤ b := by exact_mod_cast hB
    have := geom_lt b hb N
    exact_mod_cast this
  have := (abs_le.1 hlow).1
  linarith

end

end L90

end Jones1980
