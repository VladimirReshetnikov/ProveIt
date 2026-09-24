import Diophantine.Paper1980.Isolation90a

/-!
# Coefficient isolation for the 90-operation layout, part 2: the windows

`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, Section 3 (the "exact isolation
facts" of `PRODUCT_BOUND_91_PROOF.md`, Section 3).  For a valid layout and a
tested start `r` of band `j`, the coefficients of `D · C²` at the positions
`r − 6, …, r + 2` are:

* at the target `t_j`: the row value `R_j(x, z)`, plus the square of the
  helper value if the row has the negative term `−x²` (a seed);
* at a negative position `t_j − W μ₀`: `V_helper² − x²`;
* at `r − 4`: at least `x²` (the reset, plus nonnegative reset overlaps);
* at `t_last − 1`: the padding `Σ_{h ∈ P_X} 2 x z_h`;
* zero at the remaining positions.

The multiset uniqueness of weights (`W_inj`) and the disjointness of the
helper group from the negative factors are used exactly as in the note.
-/

namespace Jones1980

namespace L90

open Polynomial Finset
open Layout (Row)
open Iso (contrib coeff_mul_eq_zero_of_lt)

noncomputable section

variable {m s : ℕ} (rows : Fin s → Row m) (hel : Fin s → Fin 3 → Fin m) (PX : Finset (Fin m))
  (x : ℤ) (z : Fin m → ℤ)

/-! ### List sums with unique keys -/

theorem sum_map_ite_key {α β : Type*} [DecidableEq α] (f : β → ℤ) :
    ∀ (l : List (α × β)), (l.map Prod.fst).Nodup → ∀ {a : α} {b : β}, (a, b) ∈ l →
      (l.map fun q => if q.1 = a then f q.2 else 0).sum = f b
  | [], _, _, _, hab => by simp at hab
  | q :: l, hnd, a, b, hab => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    have hmem : ∀ q' ∈ l, q'.1 ∈ l.map Prod.fst := fun q' hq' => List.mem_map_of_mem hq'
    rcases List.mem_cons.1 hab with h | hab'
    · subst h
      rw [if_pos rfl]
      have : (l.map fun q => if q.1 = a then f q.2 else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨q', hq', rfl⟩ := hy
        have hne : q'.1 ≠ a := fun h => hnd.1 (h ▸ hmem q' hq')
        rw [if_neg hne]
      rw [this, add_zero]
    · have hne : q.1 ≠ a := fun h => hnd.1 (h ▸ hmem _ hab')
      rw [if_neg hne, zero_add]
      exact sum_map_ite_key f l hnd.2 hab'

theorem sum_map_ite_eq {α : Type*} [DecidableEq α] (c : ℤ) :
    ∀ (l : List α), l.Nodup → ∀ a : α,
      (l.map fun b => if b = a then c else 0).sum = if a ∈ l then c else 0
  | [], _, a => by simp
  | b :: l, hnd, a => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons, sum_map_ite_eq c l hnd.2 a]
    by_cases hba : b = a
    · subst hba
      rw [if_pos rfl, if_neg hnd.1, if_pos (List.mem_cons_self ..)]; ring
    · rw [if_neg hba, zero_add]
      by_cases hal : a ∈ l
      · rw [if_pos hal, if_pos (List.mem_cons_of_mem _ hal)]
      · rw [if_neg hal, if_neg]
        intro h
        rcases List.mem_cons.1 h with h | h
        · exact hba h.symm
        · exact hal h

/-! ### The `x²` term -/

theorem zero_mem_terms_iff {R : Row m} {c : ℤ} :
    ((0 : Multiset (Fin m)), c) ∈ terms R ↔ c = R.xx := by
  unfold terms
  simp only [List.mem_append, List.mem_map, List.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (((⟨p, _, h, _⟩ | ⟨p, _, h, _⟩) | ⟨p, _, h, _⟩) | ⟨_, h⟩)
    · exfalso; rw [Multiset.insert_eq_cons] at h; exact Multiset.cons_ne_zero h
    · exfalso; rw [Multiset.insert_eq_cons] at h; exact Multiset.cons_ne_zero h
    · exfalso; exact Multiset.singleton_ne_zero _ h
    · exact h
  · intro h; right; exact ⟨trivial, h⟩

theorem zero_mem_negs_iff {R : Row m} : (0 : Multiset (Fin m)) ∈ negs R ↔ R.xx < 0 := by
  rw [mem_negs]
  constructor
  · rintro ⟨c, hc, hneg⟩; rw [zero_mem_terms_iff.1 hc] at hneg; exact hneg
  · intro h; exact ⟨R.xx, zero_mem_terms_iff.2 rfl, h⟩

/-! ### The main terms at a start -/

/-- At the target, the main terms give the row value. -/
theorem main_at_target (j : ℕ) (R : Row m) (hcross : ∀ q ∈ R.cross, q.1 ≠ q.2.1)
    (hM : 2 * M m ≤ t m s j) :
    ((terms R).map fun q => contrib q.2 (t m s j - W q.1) (t m s j) (Cmain x z ^ 2)).sum =
      R.val x z := by
  rw [← terms_sum_eq_val x z R hcross]
  congr 1
  apply List.map_congr_left
  intro q hq
  have hw := W_le_two_M_of_mem_terms hq
  rw [contrib_of_le x z (by omega), Nat.sub_sub_self (by omega)]

/-- At a negative position of degree two, the main terms give `−x²`. -/
theorem main_at_neg (j : ℕ) {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P)
    {μ₀ : Multiset (Fin m)} (hμ₀ : μ₀ ∈ negs R) (h2 : Multiset.card μ₀ = 2)
    (hM : 2 * M m ≤ t m s j) :
    ((terms R).map fun q => contrib q.2 (t m s j - W q.1) (t m s j - W μ₀) (Cmain x z ^ 2)).sum =
      -x ^ 2 := by
  obtain ⟨c₀, hc₀, _⟩ := (mem_negs).1 hμ₀
  have hc₀' : c₀ = -1 := coeff_of_mem_negs hR hc₀ hμ₀
  have hw0 := W_le_two_M_of_mem_negs hμ₀
  have key : ∀ q ∈ terms R,
      contrib q.2 (t m s j - W q.1) (t m s j - W μ₀) (Cmain x z ^ 2) =
        if q.1 = μ₀ then q.2 * x ^ 2 else 0 := by
    intro q hq
    have hw := W_le_two_M_of_mem_terms hq
    split_ifs with hq0
    · rw [hq0, contrib_of_le x z le_rfl, Nat.sub_self, coeff_Cmain_sq_zero]
    · by_contra hne
      obtain ⟨hle, ν, hν, hp⟩ := contrib_ne_zero_imp x z hne
      have hW : W q.1 = W (μ₀ + ν) := by rw [W_add]; omega
      have hcard := card_le_two_of_mem_terms hq
      have heq := W_inj (by omega) (by rw [Multiset.card_add]; omega) hW
      have hc : Multiset.card ν = 0 := by
        have := congrArg Multiset.card heq; rw [Multiset.card_add] at this; omega
      rw [Multiset.card_eq_zero.1 hc, add_zero] at heq
      exact hq0 heq
  rw [List.map_congr_left key, sum_map_ite_key (fun c => c * x ^ 2) (terms R) hR.nodup hc₀, hc₀']
  ring

/-! ### The helper complements at a start -/

/-- At the target, the helper complements give the helper square exactly when the row has
the negative term `−x²`. -/
theorem help_at_target (j : ℕ) {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P)
    (hM : 4 * M m ≤ t m s j) :
    ((negs R).map fun μ => ((pairs P).map fun π =>
      contrib 1 (t m s j - W μ - W π) (t m s j) (Cmain x z ^ 2)).sum).sum =
      if R.xx < 0 then S P z ^ 2 else 0 := by
  have key : ∀ μ ∈ negs R, ((pairs P).map fun π =>
      contrib 1 (t m s j - W μ - W π) (t m s j) (Cmain x z ^ 2)).sum =
        if μ = 0 then S P z ^ 2 else 0 := by
    intro μ hμ
    have hw := W_le_two_M_of_mem_negs hμ
    split_ifs with hμ0
    · subst hμ0
      rw [← pairs_sum_eq_sq x z P hR.inj]
      congr 1; apply List.map_congr_left
      intro π hπ
      have hwπ := W_le_two_M_of_mem_pairs hπ
      rw [W_zero, Nat.sub_zero, contrib_of_le x z (by omega), Nat.sub_sub_self (by omega), one_mul]
    · apply List.sum_eq_zero
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨π, hπ, rfl⟩ := hy
      by_contra hne
      obtain ⟨hle, ν, hν, hp⟩ := contrib_ne_zero_imp x z hne
      have hwπ := W_le_two_M_of_mem_pairs hπ
      have hW : W (μ + π) = W ν := by rw [W_add]; omega
      have hcπ := card_of_mem_pairs hπ
      rcases card_of_mem_negs hR hμ with hc | hc
      · have heq := W_inj (by rw [Multiset.card_add]; omega) (by omega) hW
        have := congrArg Multiset.card heq; rw [Multiset.card_add] at this; omega
      · exact hμ0 hc
  rw [List.map_congr_left key, sum_map_ite_eq (S P z ^ 2) (negs R) (negs_nodup hR) 0]
  by_cases h : R.xx < 0
  · rw [if_pos h, if_pos (zero_mem_negs_iff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (zero_mem_negs_iff.1 h'))]

/-- At a negative position of degree two, the helper complements give the helper square. -/
theorem help_at_neg (j : ℕ) {R : Row m} {P : Fin 3 → Fin m} (hR : RowOk R P)
    {μ₀ : Multiset (Fin m)} (hμ₀ : μ₀ ∈ negs R) (h2 : Multiset.card μ₀ = 2)
    (hM : 4 * M m ≤ t m s j) :
    ((negs R).map fun μ => ((pairs P).map fun π =>
      contrib 1 (t m s j - W μ - W π) (t m s j - W μ₀) (Cmain x z ^ 2)).sum).sum =
      S P z ^ 2 := by
  have hw0 := W_le_two_M_of_mem_negs hμ₀
  have key : ∀ μ ∈ negs R, ((pairs P).map fun π =>
      contrib 1 (t m s j - W μ - W π) (t m s j - W μ₀) (Cmain x z ^ 2)).sum =
        if μ = μ₀ then S P z ^ 2 else 0 := by
    intro μ hμ
    have hw := W_le_two_M_of_mem_negs hμ
    split_ifs with hμμ
    · subst hμμ
      rw [← pairs_sum_eq_sq x z P hR.inj]
      congr 1; apply List.map_congr_left
      intro π hπ
      have hwπ := W_le_two_M_of_mem_pairs hπ
      rw [contrib_of_le x z (by omega), one_mul]
      congr 1; omega
    · apply List.sum_eq_zero
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨π, hπ, rfl⟩ := hy
      by_contra hne
      obtain ⟨hle, ν, hν, hp⟩ := contrib_ne_zero_imp x z hne
      have hwπ := W_le_two_M_of_mem_pairs hπ
      have hW : W (μ + π) = W (μ₀ + ν) := by rw [W_add, W_add]; omega
      have hcπ := card_of_mem_pairs hπ
      have hcμ : Multiset.card μ ≤ 2 := by
        rcases card_of_mem_negs hR hμ with hc | hc
        · omega
        · rw [hc]; simp
      have heq := W_inj (by rw [Multiset.card_add]; omega) (by rw [Multiset.card_add]; omega) hW
      -- the helper pair lies in `ν`, by disjointness
      have hπν : π ≤ ν := by
        rw [Multiset.le_iff_count]
        intro a
        by_cases ha : a ∈ π
        · obtain ⟨b, rfl⟩ := mem_of_mem_pairs hπ ha
          have hnot : P b ∉ μ₀ := hR.disj μ₀ hμ₀ b
          have := congrArg (Multiset.count (P b)) heq
          rw [Multiset.count_add, Multiset.count_add, Multiset.count_eq_zero.2 hnot, zero_add]
            at this
          omega
        · rw [Multiset.count_eq_zero.2 ha]; exact Nat.zero_le _
      have hπν' : π = ν := Multiset.eq_of_le_of_card_le hπν (by omega)
      rw [hπν'] at heq
      exact hμμ (add_right_cancel heq)
  rw [List.map_congr_left key, sum_map_ite_eq (S P z ^ 2) (negs R) (negs_nodup hR) μ₀,
    if_pos hμ₀]

/-! ### Residue classes -/

/-- A main or helper term (exponent `≡ 0`) contributes nothing at `p ≢ 0 (mod 8)`. -/
theorem contrib_main_zero {c : ℤ} {j w p : ℕ} (hw : 8 ∣ w) (hwt : w ≤ t m s j) (hp : ¬ 8 ∣ p) :
    contrib c (t m s j - w) p (Cmain x z ^ 2) = 0 :=
  contrib_eq_zero_of_mod x z (Nat.dvd_sub (eight_dvd_t m s j) hw) hp

/-- A reset (exponent `≡ 4`) contributes nothing at `p ≢ 4 (mod 8)`. -/
theorem contrib_reset_zero {r' p : ℕ} (h8 : 8 ∣ r') (hr4 : 8 ≤ r') (hp : p % 8 ≠ 4) :
    contrib 1 (r' - 4) p (Cmain x z ^ 2) = 0 := by
  by_contra hne
  obtain ⟨hle, ν, hν, hpe⟩ := contrib_ne_zero_imp x z hne
  have := eight_dvd_W ν
  omega

/-- A padding term (exponent `≡ 7`) contributes nothing at `p ≢ 7 (mod 8)`. -/
theorem contrib_pad_zero {u p : ℕ} (hu : 8 ∣ u) (hut : u + 1 ≤ tl m s) (hp : p % 8 ≠ 7) :
    contrib 1 (tl m s - 1 - u) p (Cmain x z ^ 2) = 0 := by
  by_contra hne
  obtain ⟨hle, ν, hν, hpe⟩ := contrib_ne_zero_imp x z hne
  have := eight_dvd_W ν
  have := eight_dvd_t m s (s - 1)
  unfold tl at *
  omega

/-- The resets of band `j` at `p ≢ 4`. -/
theorem resets_zero (j : Fin s) {p : ℕ} (hp : p % 8 ≠ 4) :
    ∑ r' ∈ starts s rows j, contrib 1 (r' - 4) p (Cmain x z ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intro r' hr'
  obtain ⟨hb1, hb2⟩ := starts_bounds rows hr'
  have := t_ge m s j
  exact contrib_reset_zero x z (eight_dvd_of_mem_starts rows hr') (by omega) hp

/-- The padding at `p ≢ 7`. -/
theorem pads_zero {p : ℕ} (hp : p % 8 ≠ 7) :
    ∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) p (Cmain x z ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intro h _
  have := v_le_M h.isLt
  have := t_ge m s (s - 1)
  exact contrib_pad_zero x z (eight_dvd_v h) (by unfold tl; omega) hp

/-- The main terms of row `j` at `p ≢ 0`. -/
theorem mains_zero (j : Fin s) {p : ℕ} (hp : ¬ 8 ∣ p) :
    ((terms (rows j)).map fun q => contrib q.2 (t m s j - W q.1) p (Cmain x z ^ 2)).sum = 0 := by
  apply List.sum_eq_zero
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  have := W_le_two_M_of_mem_terms hq
  have := t_ge m s j
  exact contrib_main_zero x z (eight_dvd_W _) (by omega) hp

/-- The helper complements of row `j` at `p ≢ 0`. -/
theorem helps_zero (j : Fin s) {p : ℕ} (hp : ¬ 8 ∣ p) :
    ((negs (rows j)).map fun μ => ((pairs (hel j)).map fun π =>
      contrib 1 (t m s j - W μ - W π) p (Cmain x z ^ 2)).sum).sum = 0 := by
  apply List.sum_eq_zero
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨μ, hμ, rfl⟩ := hy
  apply List.sum_eq_zero
  intro y' hy'
  rw [List.mem_map] at hy'
  obtain ⟨π, hπ, rfl⟩ := hy'
  have := W_le_two_M_of_mem_negs hμ
  have := W_le_two_M_of_mem_pairs hπ
  have := t_ge m s j
  rw [Nat.sub_sub]
  exact contrib_main_zero x z (dvd_add (eight_dvd_W μ) (eight_dvd_W π)) (by omega) hp

/-! ### The window values -/

variable (hL : LayoutOk s rows hel)
include hL

/-- The coefficient at the target `t_j`. -/
theorem coeff_at_target (j : Fin s) :
    (D s rows hel PX * Cmain x z ^ 2).coeff (t m s j) =
      (rows j).val x z + (if (rows j).xx < 0 then S (hel j) z ^ 2 else 0) := by
  have htj := t_ge m s j
  have hR := hL.rows_ok j
  have h8 := eight_dvd_t m s j
  rw [coeff_band_only rows hel PX x z hL j _ (by omega) (by omega),
    main_at_target x z j (rows j) hR.cross (by omega), help_at_target x z j hR (by omega),
    resets_zero rows x z j (by omega)]
  have hpad : (if (j : ℕ) = s - 1 then
      ∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) (t m s j) (Cmain x z ^ 2) else 0) = 0 := by
    split_ifs with hj
    · exact pads_zero PX x z (by omega)
    · rfl
  rw [hpad]; ring

/-- The coefficient at a negative position of degree two. -/
theorem coeff_at_neg (j : Fin s) {μ₀ : Multiset (Fin m)} (hμ₀ : μ₀ ∈ negs (rows j))
    (h2 : Multiset.card μ₀ = 2) :
    (D s rows hel PX * Cmain x z ^ 2).coeff (t m s j - W μ₀) = S (hel j) z ^ 2 - x ^ 2 := by
  have htj := t_ge m s j
  have hR := hL.rows_ok j
  have h8 := eight_dvd_t m s j
  have hw0 := W_le_two_M_of_mem_negs hμ₀
  have h8w := eight_dvd_W μ₀
  rw [coeff_band_only rows hel PX x z hL j _ (by omega) (by omega),
    main_at_neg x z j hR hμ₀ h2 (by omega), help_at_neg x z j hR hμ₀ h2 (by omega),
    resets_zero rows x z j (by omega)]
  have hpad : (if (j : ℕ) = s - 1 then
      ∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) (t m s j - W μ₀) (Cmain x z ^ 2) else 0) = 0 := by
    split_ifs with hj
    · exfalso
      have := (hL.last j hj).1
      rw [this] at hμ₀
      simp at hμ₀
    · rfl
  rw [hpad]; ring

/-- The coefficient at the reset position `r − 4` of a start is at least `x²`. -/
theorem coeff_at_reset (hx : 0 ≤ x) (hz : ∀ i, 0 ≤ z i) (j : Fin s) {r : ℕ}
    (hr : r ∈ starts s rows j) :
    x ^ 2 ≤ (D s rows hel PX * Cmain x z ^ 2).coeff (r - 4) := by
  have htj := t_ge m s j
  obtain ⟨hb1, hb2⟩ := starts_bounds rows hr
  have h8 := eight_dvd_of_mem_starts rows hr
  rw [coeff_band_only rows hel PX x z hL j _ (by omega) (by omega),
    mains_zero rows x z j (by omega), helps_zero rows hel x z j (by omega)]
  have hpad : (if (j : ℕ) = s - 1 then
      ∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) (r - 4) (Cmain x z ^ 2) else 0) = 0 := by
    split_ifs with hj
    · exact pads_zero PX x z (by omega)
    · rfl
  rw [hpad, zero_add, zero_add, add_zero]
  have hnn : ∀ r' ∈ starts s rows j, 0 ≤ contrib 1 (r' - 4) (r - 4) (Cmain x z ^ 2) := by
    intro r' _; unfold contrib; split_ifs
    · rw [one_mul]; exact coeff_Cmain_sq_nonneg x z hx hz _
    · exact le_rfl
  calc x ^ 2 = contrib 1 (r - 4) (r - 4) (Cmain x z ^ 2) := by
        rw [contrib_of_le x z le_rfl, Nat.sub_self, coeff_Cmain_sq_zero, one_mul]
    _ ≤ _ := Finset.single_le_sum hnn hr

/-- The coefficient at the padding position `t_last − 1`. -/
theorem coeff_at_pad :
    (D s rows hel PX * Cmain x z ^ 2).coeff (tl m s - 1) = ∑ h ∈ PX, 2 * x * z h := by
  have hs := hL.three_le
  obtain ⟨j, hj⟩ : ∃ j : Fin s, (j : ℕ) = s - 1 := ⟨⟨s - 1, by omega⟩, rfl⟩
  have htl : tl m s = t m s j := by unfold tl; rw [← hj]
  have htj := t_ge m s j
  have h8 := eight_dvd_t m s j
  rw [htl, coeff_band_only rows hel PX x z hL j _ (by omega) (by omega),
    mains_zero rows x z j (by omega), helps_zero rows hel x z j (by omega),
    resets_zero rows x z j (by omega), if_pos hj, ← htl]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro h _
  have hv := v_le_M h.isLt
  rw [contrib_of_le x z (by unfold tl at *; omega), one_mul]
  have : tl m s - 1 - (tl m s - 1 - v h) = v h := by unfold tl at *; omega
  rw [this, coeff_Cmain_sq_v]

/-- The coefficient vanishes at the empty positions of a window. -/
theorem coeff_at_empty (j : Fin s) {r : ℕ} (hr : r ∈ starts s rows j) (p : ℕ)
    (hp1 : r ≤ p + 6) (hp2 : p ≤ r + 2) (h0 : p ≠ r) (h4 : p + 4 ≠ r)
    (h1 : p + 1 = r → (j : ℕ) ≠ s - 1) :
    (D s rows hel PX * Cmain x z ^ 2).coeff p = 0 := by
  have htj := t_ge m s j
  obtain ⟨hb1, hb2⟩ := starts_bounds rows hr
  have h8 := eight_dvd_of_mem_starts rows hr
  rw [coeff_band_only rows hel PX x z hL j _ (by omega) (by omega),
    mains_zero rows x z j (by omega), helps_zero rows hel x z j (by omega),
    resets_zero rows x z j (by omega)]
  have hpad : (if (j : ℕ) = s - 1 then
      ∑ h ∈ PX, contrib 1 (tl m s - 1 - v h) p (Cmain x z ^ 2) else 0) = 0 := by
    split_ifs with hj
    · have : p + 1 ≠ r := fun h => h1 h hj
      exact pads_zero PX x z (by omega)
    · rfl
  rw [hpad]; ring

/-! ### Dummy exclusion -/

omit hL

theorem coeff_D_eq_zero_of_lt (h : ℕ) (hh : h + 4 * M m + 4 < t m s 0) :
    (D s rows hel PX).coeff h = 0 := by
  have ht0 : ∀ j : Fin s, t m s 0 ≤ t m s j := fun j => t_mono (Nat.zero_le _)
  have htl : t m s 0 ≤ tl m s := t_mono (Nat.zero_le _)
  unfold D
  rw [coeff_add, coeff_add, coeff_add, finsetSum_coeff, finsetSum_coeff]
  have e1 : ∑ j : Fin s, (rowPoly s j (rows j)).coeff h = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    unfold rowPoly
    rw [Iso.coeff_list_sum]
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have := W_le_two_M_of_mem_terms hq
    have := ht0 j
    rw [coeff_C_mul_X_pow, if_neg (by omega)]
  have e2 : ∑ j : Fin s, (helpPoly s j (rows j) (hel j)).coeff h = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    unfold helpPoly
    rw [Iso.coeff_list_sum]
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨μ, hμ, rfl⟩ := hy
    rw [Iso.coeff_list_sum]
    apply List.sum_eq_zero
    intro y' hy'
    rw [List.mem_map] at hy'
    obtain ⟨π, hπ, rfl⟩ := hy'
    have := W_le_two_M_of_mem_negs hμ
    have := W_le_two_M_of_mem_pairs hπ
    have := ht0 j
    rw [coeff_X_pow, if_neg (by omega)]
  have e3 : (resetPoly s rows).coeff h = 0 := by
    unfold resetPoly
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro r hr
    have := Rset_bounds rows hr
    rw [coeff_X_pow, if_neg (by omega)]
  have e4 : (padPoly s PX).coeff h = 0 := by
    unfold padPoly
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro q _
    have := v_le_M q.isLt
    have := t_ge m s 0
    rw [coeff_X_pow, if_neg (by omega)]
  rw [e1, e2, e3, e4]; ring

theorem coeff_Cdum_eq_zero_of_lt (dum : ℕ → Fin 3 → ℤ) (h : ℕ) (hh : h + 2 * M m < t m s 0) :
    (Cdum s rows dum).coeff h = 0 := by
  unfold Cdum
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro r hr
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro e _
  have := Rset_bounds rows hr
  rw [coeff_C_mul_X_pow, if_neg (by omega)]

/-- The dummy digits do not reach any position up to `t_last + 2`. -/
theorem coeff_eq_main (hs : 1 ≤ s) (dum : ℕ → Fin 3 → ℤ) (p : ℕ) (hp : p ≤ tl m s + 2) :
    (D s rows hel PX * (Cmain x z + Cdum s rows dum) ^ 2).coeff p =
      (D s rows hel PX * Cmain x z ^ 2).coeff p := by
  have hexp : (Cmain x z + Cdum s rows dum) ^ 2 =
      Cmain x z ^ 2 + (2 * Cmain x z + Cdum s rows dum) * Cdum s rows dum := by ring
  rw [hexp, mul_add, coeff_add]
  have ht0 := t_zero_ge m s
  have hD : ∀ i, i < t m s 0 - 4 * M m - 4 → (D s rows hel PX).coeff i = 0 :=
    fun i hi => coeff_D_eq_zero_of_lt rows hel PX i (by omega)
  have hC : ∀ i, i < t m s 0 - 2 * M m →
      ((2 * Cmain x z + Cdum s rows dum) * Cdum s rows dum).coeff i = 0 := by
    intro i hi
    apply coeff_mul_eq_zero_of_lt (A := 0) (B := t m s 0 - 2 * M m)
    · intro _ h; omega
    · intro j hj; exact coeff_Cdum_eq_zero_of_lt rows dum j (by omega)
    · omega
  rw [coeff_mul_eq_zero_of_lt hD hC ?_, add_zero]
  have := dummy_exclusion (m := m) (s := s) (u := t m s 0 - 2 * M m) (e := t m s 0 - 4 * M m - 4)
    hs (by omega) (by omega)
  omega

end

end L90

end Jones1980
