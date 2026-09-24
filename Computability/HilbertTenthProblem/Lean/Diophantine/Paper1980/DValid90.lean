import Diophantine.Paper1980.Isolation90b

/-!
# The coefficients of `D` for the 90-operation layout, part 1: the four kinds

`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, Section 3.  The coefficient of `X^h`
in `D` is the sum of the coefficients of the four kinds of terms: the main
terms of the rows (exponents `≡ 0 (mod 8)`, coefficients `±1`, at most one per
band), the helper complements (exponents `≡ 0`, coefficients `0` or `1`, at
most one per band by weight uniqueness and helper disjointness), the resets
(`≡ 4`, `0` or `1`) and the padding (`≡ 7`, `0` or `1`).  This file computes
the coefficients of the four parts and their basic properties.
-/

namespace Jones1980

namespace L90

open Polynomial Finset
open Layout (Row)

noncomputable section

variable {m s : ℕ} (rows : Fin s → Row m) (hel : Fin s → Fin 3 → Fin m) (PX : Finset (Fin m))

/-! ### Sums of indicators with unique keys -/

theorem sum_ite_unique {α : Type*} (g : α × ℤ → ℕ) (h : ℕ) :
    ∀ (l : List (α × ℤ)), l.Nodup → (∀ q ∈ l, ∀ q' ∈ l, g q = g q' → q = q') →
      (l.map fun q => if h = g q then q.2 else 0).sum = 0 ∨
        ∃ q ∈ l, h = g q ∧ (l.map fun q => if h = g q then q.2 else 0).sum = q.2
  | [], _, _ => Or.inl (by simp)
  | q :: l, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    have hinj' : ∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b :=
      fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    by_cases hq : h = g q
    · right
      refine ⟨q, List.mem_cons_self .., hq, ?_⟩
      rw [if_pos hq]
      have : (l.map fun q => if h = g q then q.2 else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨q', hq', rfl⟩ := hy
        have : h ≠ g q' := fun h' =>
          hnd.1 ((hinj q (List.mem_cons_self ..) q' (List.mem_cons_of_mem _ hq')
            (hq.symm.trans h')) ▸ hq')
        rw [if_neg this]
      rw [this, add_zero]
    · rw [if_neg hq, zero_add]
      rcases sum_ite_unique g h l hnd.2 hinj' with h0 | ⟨q', hq', hh, heq⟩
      · exact Or.inl h0
      · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', hh, heq⟩

theorem sum_ite_one_eq {β : Type*} (g : β → ℕ) (h : ℕ) :
    ∀ (l : List β), l.Nodup → (∀ b ∈ l, ∀ b' ∈ l, g b = g b' → b = b') →
      (l.map fun b => if h = g b then (1 : ℤ) else 0).sum = if ∃ b ∈ l, h = g b then 1 else 0
  | [], _, _ => by simp
  | b :: l, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    have hinj' : ∀ a ∈ l, ∀ c ∈ l, g a = g c → a = c :=
      fun a ha c hc => hinj a (List.mem_cons_of_mem _ ha) c (List.mem_cons_of_mem _ hc)
    rw [sum_ite_one_eq g h l hnd.2 hinj']
    by_cases hb : h = g b
    · rw [if_pos hb, if_pos (show ∃ b' ∈ b :: l, h = g b' from ⟨b, List.mem_cons_self .., hb⟩)]
      have : ¬ ∃ b' ∈ l, h = g b' := by
        rintro ⟨b', hb', hh⟩
        exact hnd.1 ((hinj b (List.mem_cons_self ..) b' (List.mem_cons_of_mem _ hb')
          (hb.symm.trans hh)) ▸ hb')
      rw [if_neg this]; norm_num
    · rw [if_neg hb, zero_add]
      by_cases hex : ∃ b' ∈ l, h = g b'
      · obtain ⟨b', hb', hh⟩ := hex
        rw [if_pos ⟨b', hb', hh⟩, if_pos ⟨b', List.mem_cons_of_mem _ hb', hh⟩]
      · rw [if_neg hex, if_neg]
        rintro ⟨b', hb', hh⟩
        rcases List.mem_cons.1 hb' with rfl | hb'
        · exact hb hh
        · exact hex ⟨b', hb', hh⟩

/-- A nested sum of indicators with a unique key pair. -/
theorem nested_sum_ite {α β : Type*} (l' : List β) (g : α → β → ℕ) (h : ℕ) (hl' : l'.Nodup) :
    ∀ (l : List α), l.Nodup →
      (∀ a ∈ l, ∀ b ∈ l', ∀ a' ∈ l, ∀ b' ∈ l', g a b = g a' b' → a = a' ∧ b = b') →
      (l.map fun a => (l'.map fun b => if h = g a b then (1 : ℤ) else 0).sum).sum =
        if ∃ a ∈ l, ∃ b ∈ l', h = g a b then 1 else 0
  | [], _, _ => by simp
  | a :: l, hnd, hu => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    have hu' : ∀ a ∈ l, ∀ b ∈ l', ∀ a' ∈ l, ∀ b' ∈ l', g a b = g a' b' → a = a' ∧ b = b' :=
      fun a ha b hb a' ha' b' hb' => hu a (List.mem_cons_of_mem _ ha) b hb a'
        (List.mem_cons_of_mem _ ha') b' hb'
    rw [nested_sum_ite l' g h hl' l hnd.2 hu']
    have inner : (l'.map fun b => if h = g a b then (1 : ℤ) else 0).sum =
        if ∃ b ∈ l', h = g a b then 1 else 0 := by
      apply sum_ite_one_eq (g a) h l' hl'
      intro b hb b' hb' heq
      exact (hu a (List.mem_cons_self ..) b hb a (List.mem_cons_self ..) b' hb' heq).2
    rw [inner]
    by_cases hex : ∃ b ∈ l', h = g a b
    · obtain ⟨b, hb, hh⟩ := hex
      rw [if_pos ⟨b, hb, hh⟩,
        if_pos (show ∃ a' ∈ a :: l, ∃ b' ∈ l', h = g a' b' from ⟨a, List.mem_cons_self .., b, hb, hh⟩)]
      have : ¬ ∃ a' ∈ l, ∃ b' ∈ l', h = g a' b' := by
        rintro ⟨a', ha', b', hb', hh'⟩
        exact hnd.1 ((hu a (List.mem_cons_self ..) b hb a' (List.mem_cons_of_mem _ ha') b' hb'
          (hh.symm.trans hh')).1 ▸ ha')
      rw [if_neg this]; norm_num
    · rw [if_neg hex, zero_add]
      by_cases hex' : ∃ a' ∈ l, ∃ b' ∈ l', h = g a' b'
      · obtain ⟨a', ha', b', hb', hh'⟩ := hex'
        rw [if_pos ⟨a', ha', b', hb', hh'⟩, if_pos ⟨a', List.mem_cons_of_mem _ ha', b', hb', hh'⟩]
      · rw [if_neg hex', if_neg]
        rintro ⟨a', ha', b', hb', hh'⟩
        rcases List.mem_cons.1 ha' with rfl | ha'
        · exact hex ⟨b', hb', hh'⟩
        · exact hex' ⟨a', ha', b', hb', hh'⟩

/-- A sum over a finite type whose nonzero terms have a unique index. -/
theorem sum_unique {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℤ)
    (hu : ∀ j k, f j ≠ 0 → f k ≠ 0 → j = k) :
    (∑ j, f j) = 0 ∨ ∃ j, f j ≠ 0 ∧ (∑ j, f j) = f j := by
  by_cases hex : ∃ j, f j ≠ 0
  · obtain ⟨j, hj⟩ := hex
    right
    refine ⟨j, hj, Finset.sum_eq_single j ?_ (by simp)⟩
    intro k _ hkj
    by_contra hk
    exact hkj (hu k j hk hj)
  · left
    push Not at hex
    exact Finset.sum_eq_zero fun j _ => hex j

/-! ### Multiset lemmas -/

/-- If `μ + π = μ' + ν` and the elements of `π` avoid `μ'`, then `π ≤ ν`. -/
theorem le_of_add_eq_of_disj {μ μ' π ν : Multiset (Fin m)} (hdisj : ∀ a ∈ π, a ∉ μ')
    (heq : μ + π = μ' + ν) : π ≤ ν := by
  rw [Multiset.le_iff_count]
  intro a
  by_cases ha : a ∈ π
  · have := congrArg (Multiset.count a) heq
    rw [Multiset.count_add, Multiset.count_add, Multiset.count_eq_zero.2 (hdisj a ha), zero_add]
      at this
    omega
  · rw [Multiset.count_eq_zero.2 ha]; exact Nat.zero_le _

/-! ### The parts of `D` -/

theorem coeff_rowPoly (j : ℕ) (R : Row m) (h : ℕ) :
    (rowPoly s j R).coeff h =
      ((terms R).map fun q => if h = t m s j - W q.1 then q.2 else 0).sum := by
  unfold rowPoly
  rw [Iso.coeff_list_sum]
  congr 1; apply List.map_congr_left; intro q _
  rw [coeff_C_mul_X_pow]

theorem coeff_helpPoly (j : ℕ) (R : Row m) (P : Fin 3 → Fin m) (h : ℕ) :
    (helpPoly s j R P).coeff h = ((negs R).map fun μ =>
      ((pairs P).map fun π => if h = t m s j - W μ - W π then (1 : ℤ) else 0).sum).sum := by
  unfold helpPoly
  rw [Iso.coeff_list_sum]
  congr 1; apply List.map_congr_left; intro μ _
  rw [Iso.coeff_list_sum]
  congr 1; apply List.map_congr_left; intro π _
  rw [coeff_X_pow]

theorem coeff_resetPoly (h : ℕ) :
    (resetPoly s rows).coeff h = if h + 4 ∈ Rset s rows then 1 else 0 := by
  unfold resetPoly
  rw [finsetSum_coeff]
  have : ∀ r ∈ Rset s rows, ((X : ℤ[X]) ^ (r - 4)).coeff h = if r = h + 4 then 1 else 0 := by
    intro r hr
    have := (Rset_bounds rows hr).1
    have := t_zero_ge m s
    rw [coeff_X_pow]
    by_cases hr4 : r = h + 4
    · rw [if_pos (by omega), if_pos hr4]
    · rw [if_neg (by omega), if_neg hr4]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']

theorem coeff_padPoly (h : ℕ) :
    (padPoly s PX).coeff h = ∑ q ∈ PX, if h = tl m s - 1 - v q then (1 : ℤ) else 0 := by
  unfold padPoly
  rw [finsetSum_coeff]
  exact Finset.sum_congr rfl fun q _ => by rw [coeff_X_pow]

theorem coeff_D (h : ℕ) : (D s rows hel PX).coeff h =
    ∑ j : Fin s, (rowPoly s j (rows j)).coeff h +
      ∑ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff h +
      (resetPoly s rows).coeff h + (padPoly s PX).coeff h := by
  unfold D
  rw [coeff_add, coeff_add, coeff_add, finsetSum_coeff, finsetSum_coeff]

/-! ### The main terms -/

section Rows

variable {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P) (j : ℕ) (hM : 2 * M m ≤ t m s j)
include hR hM

theorem terms_exp_inj : ∀ q ∈ terms R, ∀ q' ∈ terms R,
    t m s j - W q.1 = t m s j - W q'.1 → q = q' := by
  intro q hq q' hq' heq
  have h1 := W_le_two_M_of_mem_terms hq
  have h2 := W_le_two_M_of_mem_terms hq'
  have hW : W q.1 = W q'.1 := by omega
  have hμ := W_inj (by have := card_le_two_of_mem_terms hq; omega)
    (by have := card_le_two_of_mem_terms hq'; omega) hW
  exact List.inj_on_of_nodup_map hR.nodup hq hq' hμ

theorem coeff_rowPoly_cases (h : ℕ) :
    (rowPoly s j R).coeff h = 0 ∨
      ∃ q ∈ terms R, h = t m s j - W q.1 ∧ (rowPoly s j R).coeff h = q.2 := by
  rw [coeff_rowPoly]
  exact sum_ite_unique (fun q => t m s j - W q.1) h (terms R) (hR.nodup.of_map _)
    (terms_exp_inj hR j hM)

theorem abs_coeff_rowPoly_le (h : ℕ) : |(rowPoly s j R).coeff h| ≤ 1 := by
  rcases coeff_rowPoly_cases hR j hM h with h0 | ⟨q, hq, _, heq⟩
  · rw [h0]; norm_num
  · rw [heq]; exact hR.coeff q hq

theorem coeff_rowPoly_ne_zero {h : ℕ} (hne : (rowPoly s j R).coeff h ≠ 0) :
    8 ∣ h ∧ t m s j ≤ h + 2 * M m ∧ h ≤ t m s j := by
  rcases coeff_rowPoly_cases hR j hM h with h0 | ⟨q, hq, hh, _⟩
  · exact absurd h0 hne
  · have := W_le_two_M_of_mem_terms hq
    refine ⟨?_, by omega, by omega⟩
    rw [hh]; exact Nat.dvd_sub (eight_dvd_t m s j) (eight_dvd_W _)

theorem coeff_rowPoly_neg {h : ℕ} (hneg : (rowPoly s j R).coeff h < 0) :
    ∃ μ ∈ negs R, h = t m s j - W μ := by
  rcases coeff_rowPoly_cases hR j hM h with h0 | ⟨q, hq, hh, heq⟩
  · omega
  · exact ⟨q.1, (mem_negs).2 ⟨q.2, hq, heq ▸ hneg⟩, hh⟩

theorem coeff_rowPoly_pos {h : ℕ} (hpos : 0 < (rowPoly s j R).coeff h) :
    ∃ q ∈ terms R, 0 < q.2 ∧ h = t m s j - W q.1 := by
  rcases coeff_rowPoly_cases hR j hM h with h0 | ⟨q, hq, hh, heq⟩
  · omega
  · exact ⟨q, hq, heq ▸ hpos, hh⟩

end Rows

/-! ### The helper complements -/

section Helps

variable {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P) (j : ℕ) (hM : 4 * M m ≤ t m s j)
include hR hM

/-- Distinct helper complements have distinct exponents. -/
theorem help_exp_inj {μ μ' π π' : Multiset (Fin m)} (hμ : μ ∈ negs R) (hμ' : μ' ∈ negs R)
    (hπ : π ∈ pairs P) (hπ' : π' ∈ pairs P)
    (heq : t m s j - W μ - W π = t m s j - W μ' - W π') : μ = μ' ∧ π = π' := by
  have h1 := W_le_two_M_of_mem_negs hμ
  have h2 := W_le_two_M_of_mem_negs hμ'
  have h3 := W_le_two_M_of_mem_pairs hπ
  have h4 := W_le_two_M_of_mem_pairs hπ'
  have hW : W (μ + π) = W (μ' + π') := by rw [W_add, W_add]; omega
  have hcμ : Multiset.card μ ≤ 2 := by
    rcases card_of_mem_negs hR hμ with hc | hc
    · omega
    · rw [hc]; simp
  have hcμ' : Multiset.card μ' ≤ 2 := by
    rcases card_of_mem_negs hR hμ' with hc | hc
    · omega
    · rw [hc]; simp
  have hcπ := card_of_mem_pairs hπ
  have hcπ' := card_of_mem_pairs hπ'
  have hsum := W_inj (by rw [Multiset.card_add]; omega) (by rw [Multiset.card_add]; omega) hW
  have hle : π ≤ π' := le_of_add_eq_of_disj (fun a ha => by
    obtain ⟨b, rfl⟩ := mem_of_mem_pairs hπ ha
    exact hR.disj μ' hμ' b) hsum
  have hππ : π = π' := Multiset.eq_of_le_of_card_le hle (by omega)
  rw [hππ] at hsum
  exact ⟨add_right_cancel hsum, hππ⟩

theorem coeff_helpPoly_eq (h : ℕ) :
    (helpPoly s j R P).coeff h =
      if ∃ μ ∈ negs R, ∃ π ∈ pairs P, h = t m s j - W μ - W π then 1 else 0 := by
  rw [coeff_helpPoly]
  apply nested_sum_ite (pairs P) (fun μ π => t m s j - W μ - W π) h (pairs_nodup hR.inj)
    (negs R) (negs_nodup hR)
  intro μ hμ π hπ μ' hμ' π' hπ' heq
  exact help_exp_inj hR j hM hμ hμ' hπ hπ' heq

theorem coeff_helpPoly_bounds (h : ℕ) :
    0 ≤ (helpPoly s j R P).coeff h ∧ (helpPoly s j R P).coeff h ≤ 1 := by
  rw [coeff_helpPoly_eq hR j hM]; split_ifs <;> norm_num

theorem coeff_helpPoly_ne_zero {h : ℕ} (hne : (helpPoly s j R P).coeff h ≠ 0) :
    8 ∣ h ∧ t m s j ≤ h + 4 * M m ∧ h ≤ t m s j ∧
      ∃ μ ∈ negs R, ∃ π ∈ pairs P, h = t m s j - W μ - W π := by
  rw [coeff_helpPoly_eq hR j hM] at hne
  split_ifs at hne with hex
  · obtain ⟨μ, hμ, π, hπ, hh⟩ := hex
    have := W_le_two_M_of_mem_negs hμ
    have := W_le_two_M_of_mem_pairs hπ
    refine ⟨?_, by omega, by omega, μ, hμ, π, hπ, hh⟩
    rw [hh, Nat.sub_sub]
    exact Nat.dvd_sub (eight_dvd_t m s j) (dvd_add (eight_dvd_W μ) (eight_dvd_W π))
  · exact absurd rfl hne

end Helps

/-! ### Resets and padding -/

theorem coeff_resetPoly_bounds (h : ℕ) :
    0 ≤ (resetPoly s rows).coeff h ∧ (resetPoly s rows).coeff h ≤ 1 := by
  rw [coeff_resetPoly]; split_ifs <;> norm_num

theorem coeff_resetPoly_ne_zero {h : ℕ} (hne : (resetPoly s rows).coeff h ≠ 0) :
    h % 8 = 4 ∧ h + 4 ∈ Rset s rows := by
  rw [coeff_resetPoly] at hne
  split_ifs at hne with hmem
  · obtain ⟨j, hj⟩ := (mem_Rset s rows).1 hmem
    have := eight_dvd_of_mem_starts rows hj
    exact ⟨by omega, hmem⟩
  · exact absurd rfl hne

theorem coeff_padPoly_bounds (h : ℕ) :
    0 ≤ (padPoly s PX).coeff h ∧ (padPoly s PX).coeff h ≤ 1 := by
  rw [coeff_padPoly]
  constructor
  · exact Finset.sum_nonneg fun q _ => by split_ifs <;> norm_num
  · rw [Finset.sum_boole]
    norm_cast
    apply Finset.card_le_one.2
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have := v_le_M a.isLt
    have := v_le_M b.isLt
    have := t_ge m s (s - 1)
    have : v a = v b := by unfold tl at ha hb; omega
    exact Fin.ext (v_inj this)

theorem coeff_padPoly_ne_zero {h : ℕ} (hne : (padPoly s PX).coeff h ≠ 0) :
    h % 8 = 7 ∧ h + 9 ≤ tl m s := by
  rw [coeff_padPoly] at hne
  obtain ⟨q, _, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hne' with hh
  · have := v_le_M q.isLt
    have := eight_le_v q
    have := t_ge m s (s - 1)
    have := eight_dvd_v q
    have := eight_dvd_t m s (s - 1)
    unfold tl at hh ⊢
    constructor <;> omega
  · exact absurd rfl hne'

end

end L90

end Jones1980
