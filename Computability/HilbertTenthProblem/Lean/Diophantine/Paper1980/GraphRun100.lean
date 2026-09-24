import Diophantine.Paper1980.GraphRom100

/-!
# Recovering a path through the graph

`EXPLORATION_NONDETERMINISTIC_PROGRAM_ROUTING.md`, §5: *"At the marker block `d, …, d+l−1`,
`g Next` has no support ... `V` has zero digits at all marker positions except possibly `d`.
Its digit at `d` is Boolean.  Consequently the marker block of the right side of (7) is zero
or one.  Section 1 identifies the same normalized block on the left as `|U_j|`.  It follows
that every row of `C` contains at most one state.  ...  If any source row were empty, its `KC`
row would be zero ... Every later source row would then be empty by induction, contradicting
the fixed singleton final row.  ...  For a singleton source `i`, ... at the target `d + a_j` its
digit is one precisely when `(i, j)` is an allowed edge.  A singleton `Next` at `j` contributes
one there on the right of (7).  Hence `(i, j)` must be an allowed edge."*

`path_run` proves that argument from the route `K C = g·Next + V` and the support facts,
without any promise that the rows are single states or that the chosen branches are allowed.
-/

namespace Jones1980

open Ternary Finset

/-- A block whose inner digits vanish is its bottom digit. -/
theorem block_eq_digit {X d s : ℕ} (hs : 1 ≤ s)
    (h : ∀ k, 0 < k → k < s → dg X (d + k) = 0) : X / 3 ^ d % 3 ^ s = dg X d := by
  rw [← Ternary.val_dg_eq_mod (X / 3 ^ d) s]
  unfold Ternary.val
  rw [Finset.sum_eq_single 0]
  · rw [Ternary.dg_div_pow, Nat.add_zero, pow_zero, mul_one]
  · intro k hk hk0
    rw [Ternary.dg_div_pow, h k (by omega) (Finset.mem_range.1 hk), zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.2 (by omega)) h0

namespace Graph

variable (Gr : Graph)

/-- A selected word has no digit below the spacing. -/
theorem dg_selWord_lt {U : Finset ℕ} {k : ℕ} (hk : k < Gr.sp) : dg (Gr.selWord U) k = 0 := by
  rw [Gr.selWord_eq_image, Ternary.dg_sum_pow, if_neg]
  intro hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hmem
  have h1 := one_le_coord' i
  have h2 : Gr.sp ≤ Gr.sp * coord i := Nat.le_mul_of_pos_right _ h1
  omega

set_option maxHeartbeats 1000000 in
/-- **The path recovery.**  Every row of the state word selects exactly one state, and each
step from a row to the next-state word's row follows a permitted edge. -/
theorem path_run {C Nx V m u : ℕ} (hu : 1 ≤ u)
    (hroute : Gr.romK * C = Gr.romg * Nx + V)
    (hCfit : ∀ k, Gr.romK * row C m k < 3 ^ m) (hCb : C < 3 ^ (m * u))
    (hgfit : ∀ k, Gr.romg * row Nx m k < 3 ^ m) (hNb : Nx < 3 ^ (m * u))
    (hgN : Bool3 (Gr.romg * Nx)) (hVb : Bool3 V)
    (hCbool : Bool3 C) (hNbool : Bool3 Nx)
    (hCsup : ∀ j p, j < u → dg (row C m j) p ≤ dg Gr.romS p)
    (hNsup : ∀ j p, j < u → dg (row Nx m j) p ≤ dg Gr.romS p)
    (hshift : ∀ j, j + 1 < u → row Nx m j = row C m (j + 1))
    (htop : row Nx m (u - 1) = 3 ^ (Gr.sp * coord 0))
    (hVoff : ∀ j k, j < u → 0 < k → k < Gr.sp → dg V (m * j + (Gr.sp * Gr.bmark + k)) = 0)
    (hspan : Gr.sp * (Gr.bmark + Gr.bz) < m) :
    (∀ j, j < u → ∃ i, i < Gr.n ∧ row C m j = 3 ^ (Gr.sp * coord i)) ∧
    (∀ j i i', j < u → i < Gr.n → i' < Gr.n → row C m j = 3 ^ (Gr.sp * coord i) →
      row Nx m j = 3 ^ (Gr.sp * coord i') → Gr.adj i i' = true) := by
  have hadd : ∀ p, dg (Gr.romg * Nx) p + dg V p ≤ 2 := fun p => by
    have := hgN p
    have := hVb p
    omega
  -- ## the rowwise digit identity
  have hcorr : ∀ j p, j < u → p < m →
      dg (Gr.romK * row C m j) p = dg (Gr.romg * row Nx m j) p + dg V (m * j + p) := by
    intro j p hj hp
    have h1 : dg (Gr.romK * row C m j) p = dg (Gr.romK * C) (m * j + p) := by
      rw [← row_mul hCfit hCb hj, Ternary.dg_row _ j hp]
    have h2 : dg (Gr.romg * row Nx m j) p = dg (Gr.romg * Nx) (m * j + p) := by
      rw [← row_mul hgfit hNb hj, Ternary.dg_row _ j hp]
    rw [h1, h2, hroute, Ternary.dg_add_of_le_two hadd]
  have hbmz : Gr.bmark < Gr.bz := by have := Gr.bz_high; unfold bmark; omega
  have hbz1 : 1 ≤ Gr.bz := by omega
  have hdm : Gr.sp * Gr.bmark + Gr.sp ≤ Gr.sp * (Gr.bmark + Gr.bz) := by nlinarith
  have hsp := Gr.sp_pos
  -- ## rows are selected words
  obtain ⟨UC, hUC⟩ : ∃ U : ℕ → Finset ℕ,
      U = fun j => (range Gr.n).filter (fun i => dg (row C m j) (Gr.sp * coord i) = 1) :=
    ⟨_, rfl⟩
  have hUCj : ∀ j, UC j = (range Gr.n).filter (fun i => dg (row C m j) (Gr.sp * coord i) = 1) :=
    fun j => by rw [hUC]
  have hCsel : ∀ j, j < u → row C m j = Gr.selWord (UC j) := fun j hj => by
    rw [hUCj j]
    exact Gr.eq_selWord (hCbool.row m j) (fun p => hCsup j p hj)
  have hNsel : ∀ j, j < u → ∃ U : Finset ℕ, row Nx m j = Gr.selWord U := fun j hj =>
    ⟨_, Gr.eq_selWord (hNbool.row m j) (fun p => hNsup j p hj)⟩
  -- ## at most one state per row
  have hle1 : ∀ j, j < u → (UC j).card ≤ 1 := by
    intro j hj
    obtain ⟨UN, hUN⟩ := hNsel j hj
    have hsub : UC j ⊆ range Gr.n := by rw [hUCj j]; exact Finset.filter_subset _ _
    have hcount := Gr.count_marker hsub
    rw [← hCsel j hj] at hcount
    have hblock := block_eq_digit (X := Gr.romK * row C m j) (d := Gr.sp * Gr.bmark)
      (s := Gr.sp) (by omega) (fun k hk0 hks => by
        rw [hcorr j _ hj (by omega), show Gr.romg = 3 ^ (Gr.sp * Gr.bmark) from rfl,
          Ternary.dg_mul_pow_add, hUN, Gr.dg_selWord_lt hks, hVoff j k hj hk0 hks])
    rw [hblock] at hcount
    have hd := hcorr j (Gr.sp * Gr.bmark) hj (by omega)
    have hg0 : dg (Gr.romg * row Nx m j) (Gr.sp * Gr.bmark) = 0 := by
      have e := Ternary.dg_mul_pow_add (row Nx m j) (Gr.sp * Gr.bmark) 0
      rw [Nat.add_zero] at e
      rw [show Gr.romg = 3 ^ (Gr.sp * Gr.bmark) from rfl, e, hUN, Gr.dg_selWord_lt hsp]
    have hv := hVb (m * j + Gr.sp * Gr.bmark)
    omega
  -- ## an empty row empties the next
  have hzero : ∀ j, j < u → row C m j = 0 → row Nx m j = 0 := by
    intro j hj h0
    have hdig : ∀ p, p < m → dg (Gr.romg * row Nx m j) p = 0 := fun p hp => by
      have h := hcorr j p hj hp
      rw [h0, Nat.mul_zero] at h
      have h00 : dg 0 p = 0 := by simp [Ternary.dg]
      omega
    have hlt := hgfit j
    have heq : Gr.romg * row Nx m j = 0 :=
      Ternary.eq_of_dg_eq hlt (by positivity) (fun p => by
        rcases Nat.lt_or_ge p m with hp | hp
        · rw [hdig p hp]; simp [Ternary.dg]
        · rw [Ternary.dg_eq_zero_of_lt
            (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hp))]
          simp [Ternary.dg])
    have hg : 0 < Gr.romg := by unfold romg; positivity
    rcases Nat.mul_eq_zero.1 heq with h | h
    · omega
    · exact h
  -- ## so no row is empty
  have hne : ∀ t j, j + t = u - 1 → row C m j ≠ 0 := by
    intro t
    induction t with
    | zero =>
      intro j hj h0
      have h1 := hzero j (by omega) h0
      rw [show j = u - 1 by omega, htop] at h1
      exact absurd h1 (ne_of_gt (by positivity))
    | succ t ih =>
      intro j hj h0
      have hj1 : j + 1 < u := by omega
      have h1 := hzero j (by omega) h0
      rw [hshift j hj1] at h1
      exact ih (j + 1) (by omega) h1
  refine ⟨fun j hj => ?_, fun j i i' hj hi hi' hCi hNi' => ?_⟩
  -- ## every row is a single state
  · have hc := hle1 j hj
    have hnz := hne (u - 1 - j) j (by omega)
    have hpos : (UC j).card ≠ 0 := by
      intro hc0
      rw [Finset.card_eq_zero] at hc0
      apply hnz
      rw [hCsel j hj, hc0]
      simp [Graph.selWord]
    have hc1 : (UC j).card = 1 := by omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hc1
    have himem : i ∈ UC j := by rw [hi]; exact Finset.mem_singleton_self i
    rw [hUCj j] at himem
    refine ⟨i, Finset.mem_range.1 (Finset.mem_filter.1 himem).1, ?_⟩
    rw [hCsel j hj, hi]
    simp [Graph.selWord]
  -- ## and each step is a permitted edge
  · have hci' := Gr.coord_le_bmark hi'
    have hp : Gr.sp * (Gr.bmark + coord i') < m :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hspan
    have h1 := hcorr j _ hj hp
    rw [hCi, hNi', Nat.mul_comm Gr.romK (3 ^ (Gr.sp * coord i)),
      Gr.dg_single_target hi hi'] at h1
    have h2 : dg (Gr.romg * 3 ^ (Gr.sp * coord i')) (Gr.sp * (Gr.bmark + coord i')) = 1 := by
      have e : Gr.romg * 3 ^ (Gr.sp * coord i') = 3 ^ (Gr.sp * (Gr.bmark + coord i')) := by
        unfold romg
        rw [← pow_add, Nat.mul_add]
      rw [e, Ternary.dg_pow, if_pos rfl]
    rw [h2] at h1
    by_contra hna
    rw [if_neg hna] at h1
    omega

end Graph

end Jones1980
