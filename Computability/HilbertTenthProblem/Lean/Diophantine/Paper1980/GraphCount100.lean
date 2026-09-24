import Diophantine.Paper1980.Graph100

/-!
# The count marker

`EXPLORATION_NONDETERMINISTIC_PROGRAM_ROUTING.md`, §1: *"Consider any source subset `U`, with
word `c_U = Σ_{i∈U} 3^(a_i)`.  Before normalization, the coefficient of `K(T) c_U(T)` at the
marker position `d` is exactly `|U|`.  ...  At an ordinary target `d + a_j`, the raw coefficient
is the number of edges from `U` to `j`.  ...  Since `3^l > m`, there is no carry between
adjacent base-`3^l` blocks.  In particular the complete normalized block of length `l` starting
at `d` is the ordinary ternary representation of `|U|`."*

For a single selected state `i`, the product `3^(sp·3^i) · K` is a shift of the Boolean table,
so its digit at a target column `sp(bmark + 3^j)` is one exactly when `i → j` is permitted
(`dg_single_target`), its marker digit is one, its port digits are the labels, and it has no
digit off the grid.

For a set `U` of selected states the products overlap, so the ternary digits can carry; but
every exponent is a multiple of `sp`, and at any block the number of contributions is at most
`|U| < 3^sp`.  Read in base `3^sp`, the product is therefore a numeral whose block digits are
those counts, and the block at the marker is exactly `|U|` (`count_marker`).
-/

namespace Jones1980

open Ternary Finset

namespace Graph

variable (Gr : Graph)

/-- The fixed state word. -/
def romS : ℕ := ∑ i ∈ range Gr.n, 3 ^ (Gr.sp * coord i)

theorem sp_pos : 0 < Gr.sp := by have := Gr.sp_ge; omega

theorem coord_inj' {i j : ℕ} (h : coord i = coord j) : i = j := Controller.coord_inj h

theorem romS_eq_image : Gr.romS = ∑ e ∈ (range Gr.n).image (fun i => Gr.sp * coord i), 3 ^ e := by
  unfold romS
  rw [Finset.sum_image]
  intro i _ j _ h
  exact coord_inj' (Nat.eq_of_mul_eq_mul_left Gr.sp_pos h)

theorem dg_romS (p : ℕ) :
    dg Gr.romS p = if p ∈ (range Gr.n).image (fun i => Gr.sp * coord i) then 1 else 0 := by
  rw [Gr.romS_eq_image]
  exact Ternary.dg_sum_pow _ p

theorem romS_bool : Bool3 Gr.romS := by
  rw [Gr.romS_eq_image]
  exact Ternary.bool3_sum_pow _

theorem mem_scaled {E : ℕ} : Gr.sp * E ∈ Gr.bexpSet.image (fun E => Gr.sp * E) ↔ E ∈ Gr.bexpSet := by
  constructor
  · intro h
    obtain ⟨E', hE', hEq⟩ := Finset.mem_image.1 h
    rwa [← Nat.eq_of_mul_eq_mul_left Gr.sp_pos hEq]
  · exact fun h => Finset.mem_image.2 ⟨E, h, rfl⟩

/-! ### A single selected state -/

/-- The digit of a single state's product at a grid column. -/
theorem dg_single {i X : ℕ} :
    dg (3 ^ (Gr.sp * coord i) * Gr.romK) (Gr.sp * X)
      = if coord i ≤ X ∧ X - coord i ∈ Gr.bexpSet then 1 else 0 := by
  by_cases hle : coord i ≤ X
  · have hpos : Gr.sp * X = Gr.sp * coord i + Gr.sp * (X - coord i) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [hpos, Ternary.dg_mul_pow_add, Gr.dg_romK]
    by_cases hm : X - coord i ∈ Gr.bexpSet
    · rw [if_pos ((Gr.mem_scaled).2 hm), if_pos ⟨hle, hm⟩]
    · rw [if_neg (fun h => hm ((Gr.mem_scaled).1 h)), if_neg (fun h => hm h.2)]
  · rw [Ternary.dg_mul_pow_of_lt _ (Nat.mul_lt_mul_left Gr.sp_pos |>.2 (by omega)),
      if_neg (fun h => hle h.1)]

/-- A single state's product has no digit off the grid. -/
theorem dg_single_offgrid {i p : ℕ} (hp : p % Gr.sp ≠ 0) :
    dg (3 ^ (Gr.sp * coord i) * Gr.romK) p = 0 := by
  by_cases hlt : p < Gr.sp * coord i
  · exact Ternary.dg_mul_pow_of_lt _ hlt
  · have hsplit : p = Gr.sp * coord i + (p - Gr.sp * coord i) := by omega
    rw [hsplit, Ternary.dg_mul_pow_add, Gr.dg_romK, if_neg]
    intro h
    obtain ⟨E, -, hE⟩ := Finset.mem_image.1 h
    apply hp
    have : p = Gr.sp * (coord i + E) := by rw [Nat.mul_add]; omega
    rw [this, Nat.mul_mod_right]

/-- The target block exponent `bmark + 3^j − 3^i` is in the table exactly for a permitted
edge. -/
theorem target_mem_iff {i j : ℕ} (hi : i < Gr.n) (hj : j < Gr.n) :
    Gr.bmark + coord j - coord i ∈ Gr.bexpSet ↔ Gr.adj i j = true := by
  have hci := Gr.coord_le_bmark hi
  have hcj := Gr.coord_le_bmark hj
  have hm : Gr.bmark = 3 ^ (Gr.n - 1) := rfl
  have hbs := Gr.bs_high
  have hbz := Gr.bz_high
  constructor
  · intro hmem
    unfold bexpSet at hmem
    rcases Finset.mem_union.1 hmem with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · rcases Finset.mem_union.1 h' with h'' | h''
        · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 h''
          have ha := (Gr.mem_edges).1 hp
          have hp1 := Gr.coord_le_bmark (Gr.adj_lt _ _ ha).1
          unfold edgeE at hpe
          have hsum : coord p.2 + coord i = coord j + coord p.1 := by omega
          rcases sidon_coord hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h2, ← h1]; exact ha
          · rw [h1, Gr.adj_irrefl] at ha
            exact absurd ha (by simp)
        · obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h''
          have hk' := Gr.coord_le_bmark (Finset.mem_range.1 hk)
          unfold markE at hke
          have hsum : coord j + coord k = coord i := by omega
          exact absurd hsum (pow_add_pow_ne_pow _ _ _)
      · obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h'
        have := (Gr.sgnE_bounds (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)).1
        omega
    · obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h
      have := (Gr.zreqE_bounds (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)).1
      omega
  · intro ha
    unfold bexpSet
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
    exact Finset.mem_image.2 ⟨(i, j), (Gr.mem_edges).2 ha, rfl⟩

/-- The marker block exponent is always in the table. -/
theorem marker_mem {i : ℕ} (hi : i < Gr.n) : Gr.bmark - coord i ∈ Gr.bexpSet := by
  unfold bexpSet
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩)))

/-- The sign port block exponent is in the table exactly for a sign-labelled state. -/
theorem sgn_mem_iff {i : ℕ} (hi : i < Gr.n) :
    Gr.bmark + Gr.bs - coord i ∈ Gr.bexpSet ↔ Gr.sgn i = true := by
  have hci := Gr.coord_le_bmark hi
  have hc1 := one_le_coord' i
  have hm : Gr.bmark = 3 ^ (Gr.n - 1) := rfl
  have hbs := Gr.bs_high
  have hbz := Gr.bz_high
  constructor
  · intro hmem
    unfold bexpSet at hmem
    rcases Finset.mem_union.1 hmem with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · rcases Finset.mem_union.1 h' with h'' | h''
        · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 h''
          have := Gr.edgeE_le hp
          omega
        · obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h''
          have := Gr.markE_lt (Finset.mem_range.1 hk)
          omega
      · obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h'
        have hk' := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
        have hck := Gr.coord_le_bmark hk'
        unfold sgnE at hke
        have : k = i := coord_inj' (by omega)
        rw [← this]
        exact (Finset.mem_filter.1 hk).2
    · obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h
      have := (Gr.zreqE_bounds (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)).1
      omega
  · intro hs
    unfold bexpSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hs⟩, rfl⟩))

/-- The zero-request port block exponent is in the table exactly for a no-zero-request
state. -/
theorem zreq_mem_iff {i : ℕ} (hi : i < Gr.n) :
    Gr.bmark + Gr.bz - coord i ∈ Gr.bexpSet ↔ Gr.zreq i = true := by
  have hci := Gr.coord_le_bmark hi
  have hc1 := one_le_coord' i
  have hm : Gr.bmark = 3 ^ (Gr.n - 1) := rfl
  have hbs := Gr.bs_high
  have hbz := Gr.bz_high
  constructor
  · intro hmem
    unfold bexpSet at hmem
    rcases Finset.mem_union.1 hmem with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · rcases Finset.mem_union.1 h' with h'' | h''
        · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 h''
          have := Gr.edgeE_le hp
          omega
        · obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h''
          have := Gr.markE_lt (Finset.mem_range.1 hk)
          omega
      · obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h'
        have := (Gr.sgnE_bounds (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)).2
        omega
    · obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 h
      have hk' := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
      have hck := Gr.coord_le_bmark hk'
      unfold zreqE at hke
      have : k = i := coord_inj' (by omega)
      rw [← this]
      exact (Finset.mem_filter.1 hk).2
  · intro hz
    unfold bexpSet
    exact Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hz⟩, rfl⟩)

/-- **The projection of a single state at a target column.** -/
theorem dg_single_target {i j : ℕ} (hi : i < Gr.n) (hj : j < Gr.n) :
    dg (3 ^ (Gr.sp * coord i) * Gr.romK) (Gr.sp * (Gr.bmark + coord j))
      = if Gr.adj i j = true then 1 else 0 := by
  have hci := Gr.coord_le_bmark hi
  rw [Gr.dg_single]
  have hsub : Gr.bmark + coord j - coord i = Gr.bmark + coord j - coord i := rfl
  by_cases ha : Gr.adj i j = true
  · rw [if_pos ⟨by omega, (Gr.target_mem_iff hi hj).2 ha⟩, if_pos ha]
  · rw [if_neg (fun h => ha ((Gr.target_mem_iff hi hj).1 h.2)), if_neg ha]

/-- The marker digit of a single state's product is one. -/
theorem dg_single_marker {i : ℕ} (hi : i < Gr.n) :
    dg (3 ^ (Gr.sp * coord i) * Gr.romK) (Gr.sp * Gr.bmark) = 1 := by
  have hci := Gr.coord_le_bmark hi
  rw [Gr.dg_single, if_pos ⟨hci, Gr.marker_mem hi⟩]

/-- The sign port digit of a single state's product is its sign label. -/
theorem dg_single_sgn {i : ℕ} (hi : i < Gr.n) :
    dg (3 ^ (Gr.sp * coord i) * Gr.romK) (Gr.sp * (Gr.bmark + Gr.bs))
      = if Gr.sgn i = true then 1 else 0 := by
  have hci := Gr.coord_le_bmark hi
  rw [Gr.dg_single]
  by_cases hs : Gr.sgn i = true
  · rw [if_pos ⟨by omega, (Gr.sgn_mem_iff hi).2 hs⟩, if_pos hs]
  · rw [if_neg (fun h => hs ((Gr.sgn_mem_iff hi).1 h.2)), if_neg hs]

/-- The zero-request port digit of a single state's product is its no-zero-request label. -/
theorem dg_single_zreq {i : ℕ} (hi : i < Gr.n) :
    dg (3 ^ (Gr.sp * coord i) * Gr.romK) (Gr.sp * (Gr.bmark + Gr.bz))
      = if Gr.zreq i = true then 1 else 0 := by
  have hci := Gr.coord_le_bmark hi
  rw [Gr.dg_single]
  by_cases hz : Gr.zreq i = true
  · rw [if_pos ⟨by omega, (Gr.zreq_mem_iff hi).2 hz⟩, if_pos hz]
  · rw [if_neg (fun h => hz ((Gr.zreq_mem_iff hi).1 h.2)), if_neg hz]

/-! ### Words selecting sets of states -/

/-- The word selecting a set of states. -/
def selWord (U : Finset ℕ) : ℕ := ∑ i ∈ U, 3 ^ (Gr.sp * coord i)

theorem selWord_eq_image {U : Finset ℕ} :
    Gr.selWord U = ∑ e ∈ U.image (fun i => Gr.sp * coord i), 3 ^ e := by
  unfold selWord
  rw [Finset.sum_image]
  intro i _ j _ h
  exact coord_inj' (Nat.eq_of_mul_eq_mul_left Gr.sp_pos h)

/-- **A Boolean word below the fixed state word selects a set of states.** -/
theorem eq_selWord {X : ℕ} (hX : Bool3 X) (hle : ∀ p, dg X p ≤ dg Gr.romS p) :
    X = Gr.selWord ((range Gr.n).filter (fun i => dg X (Gr.sp * coord i) = 1)) := by
  obtain ⟨V, hV⟩ : ∃ V : Finset ℕ, V = (range Gr.n).filter (fun i => dg X (Gr.sp * coord i) = 1) :=
    ⟨_, rfl⟩
  rw [← hV]
  have hXN : X < 3 ^ (X + Gr.selWord V) :=
    lt_of_le_of_lt (by omega) (Ternary.lt_three_pow _)
  have hSN : Gr.selWord V < 3 ^ (X + Gr.selWord V) :=
    lt_of_le_of_lt (by omega) (Ternary.lt_three_pow _)
  refine Ternary.eq_of_dg_eq hXN hSN fun p => ?_
  rw [Gr.selWord_eq_image, Ternary.dg_sum_pow]
  by_cases hp : ∃ i, i < Gr.n ∧ p = Gr.sp * coord i
  · obtain ⟨i, hi, rfl⟩ := hp
    have h1 := hX (Gr.sp * coord i)
    by_cases hd : dg X (Gr.sp * coord i) = 1
    · have hmem : i ∈ V := by
        rw [hV]
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hd⟩
      rw [hd, if_pos (Finset.mem_image.2 ⟨i, hmem, rfl⟩)]
    · rw [if_neg]
      · omega
      · intro hmem
        obtain ⟨i', hi', hEq⟩ := Finset.mem_image.1 hmem
        rw [hV] at hi'
        have hii : i' = i := coord_inj' (Nat.eq_of_mul_eq_mul_left Gr.sp_pos hEq)
        rw [hii] at hi'
        exact hd (Finset.mem_filter.1 hi').2
  · push_neg at hp
    have h0 : dg Gr.romS p = 0 := by
      rw [Gr.dg_romS, if_neg]
      intro hmem
      obtain ⟨i, hi, hEq⟩ := Finset.mem_image.1 hmem
      exact hp i (Finset.mem_range.1 hi) hEq.symm
    have := hle p
    rw [if_neg]
    · omega
    · intro hmem
      obtain ⟨i, hi, hEq⟩ := Finset.mem_image.1 hmem
      rw [hV] at hi
      exact hp i (Finset.mem_range.1 (Finset.mem_filter.1 hi).1) hEq.symm

/-! ### The count marker -/

/-- **The count marker.**  The block of `K · c_U` at the marker is exactly `|U|`. -/
theorem count_marker {U : Finset ℕ} (hU : U ⊆ range Gr.n) :
    Gr.romK * Gr.selWord U / 3 ^ (Gr.sp * Gr.bmark) % 3 ^ Gr.sp = U.card := by
  obtain ⟨T, hT⟩ : ∃ T, T = Gr.bmark + Gr.bz + Gr.bmark + 1 := ⟨_, rfl⟩
  obtain ⟨cnt, hcnt⟩ : ∃ cnt : ℕ → ℕ, cnt = fun k =>
      ((U ×ˢ Gr.bexpSet).filter (fun x => x.2 + coord x.1 = k)).card := ⟨_, rfl⟩
  -- the product as a sum over pairs
  have hprod : Gr.romK * Gr.selWord U
      = ∑ x ∈ U ×ˢ Gr.bexpSet, 3 ^ (Gr.sp * (x.2 + coord x.1)) := by
    unfold romK selWord
    rw [Finset.sum_mul_sum, Finset.sum_comm, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun E _ => ?_
    rw [← pow_add, ← Nat.mul_add, Nat.add_comm]
  -- grouped into blocks
  have hmaps : ∀ x ∈ U ×ˢ Gr.bexpSet, x.2 + coord x.1 ∈ range T := by
    intro x hx
    rw [Finset.mem_product] at hx
    have h1 := Gr.bexp_lt hx.2
    have h2 := Gr.coord_le_bmark (Finset.mem_range.1 (hU hx.1))
    rw [Finset.mem_range, hT]
    omega
  have hblocks : Gr.romK * Gr.selWord U = rowsum cnt Gr.sp T := by
    rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmaps]
    unfold rowsum
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcnt]
    simp only
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  -- every block count is small
  have hcard : ∀ k, cnt k ≤ U.card := by
    intro k
    rw [hcnt]
    refine Finset.card_le_card_of_injOn Prod.fst (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    · exact (Finset.mem_product.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1).1
    · have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
      have hy' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
      exact Prod.ext hxy (by rw [hxy] at hx'; omega)
  have hUn : U.card ≤ Gr.n := by
    have := Finset.card_le_card hU
    rwa [Finset.card_range] at this
  have hlt : ∀ k, cnt k < 3 ^ Gr.sp := fun k => by
    have := hcard k
    have := Gr.n_lt
    omega
  -- the marker block counts every selected state once
  have hmark : cnt Gr.bmark = U.card := by
    rw [hcnt]
    simp only
    have hset : (U ×ˢ Gr.bexpSet).filter (fun x => x.2 + coord x.1 = Gr.bmark)
        = U.image (fun i => (i, Gr.bmark - coord i)) := by
      ext ⟨i, E⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hi, -⟩, hE⟩
        exact ⟨i, hi, rfl, by omega⟩
      · rintro ⟨a, ha, rfl, rfl⟩
        have hca := Gr.coord_le_bmark (Finset.mem_range.1 (hU ha))
        exact ⟨⟨ha, Gr.marker_mem (Finset.mem_range.1 (hU ha))⟩, by omega⟩
    rw [hset, Finset.card_image_of_injective]
    intro a b hab
    exact congrArg Prod.fst hab
  have hbT : Gr.bmark < T := by rw [hT]; omega
  show row (Gr.romK * Gr.selWord U) Gr.sp Gr.bmark = U.card
  rw [hblocks, row_rowsum hlt T Gr.bmark hbT, hmark]

end Graph

end Jones1980
