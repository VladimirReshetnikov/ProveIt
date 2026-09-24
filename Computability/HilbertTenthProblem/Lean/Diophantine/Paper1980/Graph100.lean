import Diophantine.Paper1980.Counters100

/-!
# The nondeterministic fixed router

`EXPLORATION_NONDETERMINISTIC_PROGRAM_ROUTING.md`, §1, in the form the counter note's ROM
uses (`EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md`, §2).  The compiled universal machine
branches, so its controller is a graph, not a function: a state may have several permitted
successors, and the table carries every permitted edge.

States `i < n` get block coordinates `3^i`, with block marker `bmark = 3^(n−1)`.  The true
exponents are `sp` times block exponents, where `sp` is the grid spacing and `3^sp > n`.  The
table is

    K = Σ_{(i,j) permitted} 3^(sp(bmark + 3^j − 3^i))  +  Σ_i 3^(sp(bmark − 3^i))
        + Σ_{sign i} 3^(sp(bmark + bs − 3^i)) + Σ_{nozero i} 3^(sp(bmark + bz − 3^i)).

All its exponents are distinct: two edge exponents agree only for the same edge, by the
Sidon property and the absence of self-loops; an edge exponent never equals a marker
exponent, because a sum of two powers of three is never a power of three; the markers are
distinct; and the two port families lie above everything else.  So `K` is a Boolean ternary
numeral whose nonzero digits all sit at multiples of `sp`.

The point of the scaling is the count marker, proved in `GraphCount100.lean`: multiplied by
a word selecting any set of states, `K` produces at the marker block exactly the number of
selected states, with no carry, because that count is below `3^sp`.
-/

namespace Jones1980

open Ternary Finset

/-- A compiled nondeterministic controller: at least two states, a grid spacing wide enough
to count them, a permitted-edge relation without self-loops, sign and no-zero-request labels,
and the two port offsets in block units above everything else. -/
structure Graph where
  /-- The number of states. -/
  n : ℕ
  /-- At least two states. -/
  two_le : 2 ≤ n
  /-- The grid spacing exponent. -/
  sp : ℕ
  /-- The spacing is at least two, so the grid spacing `3^sp` is at least nine. -/
  sp_ge : 2 ≤ sp
  /-- The count marker has room for every state. -/
  n_lt : n < 3 ^ sp
  /-- The permitted edges. -/
  adj : ℕ → ℕ → Bool
  /-- Edges join states. -/
  adj_lt : ∀ i j, adj i j = true → i < n ∧ j < n
  /-- No self-loops. -/
  adj_irrefl : ∀ i, adj i i = false
  /-- The sign label. -/
  sgn : ℕ → Bool
  /-- The no-zero-request label. -/
  zreq : ℕ → Bool
  /-- The sign port offset, in block units. -/
  bs : ℕ
  /-- The zero-request port offset, in block units. -/
  bz : ℕ
  /-- The sign port sits above every edge and marker block exponent. -/
  bs_high : 2 * 3 ^ (n - 1) < bs
  /-- The zero-request port sits above every sign block exponent. -/
  bz_high : 3 ^ (n - 1) + bs < bz

namespace Graph

variable (Gr : Graph)

/-- The block marker `bmark = max_i 3^i`. -/
def bmark : ℕ := 3 ^ (Gr.n - 1)

theorem coord_le_bmark {i : ℕ} (hi : i < Gr.n) : coord i ≤ Gr.bmark :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

theorem one_le_coord' (i : ℕ) : 1 ≤ coord i := Nat.one_le_pow _ _ (by norm_num)

theorem three_le_bmark : 3 ≤ Gr.bmark := by
  have h : (3 : ℕ) ^ 1 ≤ 3 ^ (Gr.n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := Gr.two_le; omega)
  simpa [bmark] using h

/-! ### Block exponent families -/

/-- The block exponent of an edge. -/
def edgeE (p : ℕ × ℕ) : ℕ := Gr.bmark + coord p.2 - coord p.1

/-- The block exponent of a state's marker term. -/
def markE (i : ℕ) : ℕ := Gr.bmark - coord i

/-- The block exponent of a state's sign term. -/
def sgnE (i : ℕ) : ℕ := Gr.bmark + Gr.bs - coord i

/-- The block exponent of a state's no-zero-request term. -/
def zreqE (i : ℕ) : ℕ := Gr.bmark + Gr.bz - coord i

/-- The permitted edges, as a finite set of pairs. -/
def edges : Finset (ℕ × ℕ) :=
  (range Gr.n ×ˢ range Gr.n).filter (fun p => Gr.adj p.1 p.2 = true)

theorem mem_edges {p : ℕ × ℕ} : p ∈ Gr.edges ↔ Gr.adj p.1 p.2 = true := by
  unfold edges
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Gr.adj_lt _ _ h, h⟩

/-- **Edge exponents are distinct.** -/
theorem edgeE_inj {p p' : ℕ × ℕ} (hp : p ∈ Gr.edges) (hp' : p' ∈ Gr.edges)
    (h : Gr.edgeE p = Gr.edgeE p') : p = p' := by
  have ha := (Gr.mem_edges).1 hp
  have ha' := (Gr.mem_edges).1 hp'
  have h1 := Gr.coord_le_bmark (Gr.adj_lt _ _ ha).1
  have h2 := Gr.coord_le_bmark (Gr.adj_lt _ _ ha').1
  unfold edgeE at h
  have hsum : coord p.2 + coord p'.1 = coord p'.2 + coord p.1 := by omega
  rcases sidon_coord hsum with ⟨hj, hi⟩ | ⟨hji, -⟩
  · exact Prod.ext hi.symm hj
  · rw [hji, Gr.adj_irrefl] at ha
    exact absurd ha (by simp)

theorem markE_inj {i i' : ℕ} (hi : i < Gr.n) (hi' : i' < Gr.n) (h : Gr.markE i = Gr.markE i') :
    i = i' := by
  have h1 := Gr.coord_le_bmark hi
  have h2 := Gr.coord_le_bmark hi'
  unfold markE at h
  exact Controller.coord_inj (by omega)

theorem sgnE_inj {i i' : ℕ} (hi : i < Gr.n) (hi' : i' < Gr.n) (h : Gr.sgnE i = Gr.sgnE i') :
    i = i' := by
  have h1 := Gr.coord_le_bmark hi
  have h2 := Gr.coord_le_bmark hi'
  unfold sgnE at h
  exact Controller.coord_inj (by omega)

theorem zreqE_inj {i i' : ℕ} (hi : i < Gr.n) (hi' : i' < Gr.n) (h : Gr.zreqE i = Gr.zreqE i') :
    i = i' := by
  have h1 := Gr.coord_le_bmark hi
  have h2 := Gr.coord_le_bmark hi'
  unfold zreqE at h
  exact Controller.coord_inj (by omega)

/-- **No edge exponent is a marker exponent.** -/
theorem edgeE_ne_markE {p : ℕ × ℕ} {k : ℕ} (hp : p ∈ Gr.edges) (hk : k < Gr.n) :
    Gr.edgeE p ≠ Gr.markE k := by
  intro h
  have ha := (Gr.mem_edges).1 hp
  have h1 := Gr.coord_le_bmark (Gr.adj_lt _ _ ha).1
  have h2 := Gr.coord_le_bmark hk
  unfold edgeE markE at h
  have hsum : coord p.2 + coord k = coord p.1 := by omega
  exact pow_add_pow_ne_pow _ _ _ hsum

theorem edgeE_le {p : ℕ × ℕ} (hp : p ∈ Gr.edges) : Gr.edgeE p ≤ 2 * Gr.bmark := by
  have ha := (Gr.mem_edges).1 hp
  have h1 := Gr.coord_le_bmark (Gr.adj_lt _ _ ha).2
  unfold edgeE
  omega

theorem markE_lt {i : ℕ} (hi : i < Gr.n) : Gr.markE i < Gr.bmark := by
  have h1 := Gr.coord_le_bmark hi
  have h2 := one_le_coord' i
  unfold markE
  omega

theorem sgnE_bounds {i : ℕ} (hi : i < Gr.n) : Gr.bs ≤ Gr.sgnE i ∧ Gr.sgnE i < Gr.bmark + Gr.bs := by
  have h1 := Gr.coord_le_bmark hi
  have h2 := one_le_coord' i
  unfold sgnE
  omega

theorem zreqE_bounds {i : ℕ} (hi : i < Gr.n) :
    Gr.bz ≤ Gr.zreqE i ∧ Gr.zreqE i < Gr.bmark + Gr.bz := by
  have h1 := Gr.coord_le_bmark hi
  have h2 := one_le_coord' i
  unfold zreqE
  omega

/-! ### The block exponent set and the table -/

/-- The block exponents of the table. -/
def bexpSet : Finset ℕ :=
  (Gr.edges.image Gr.edgeE) ∪ ((range Gr.n).image Gr.markE)
    ∪ ((range Gr.n).filter (fun i => Gr.sgn i = true)).image Gr.sgnE
    ∪ ((range Gr.n).filter (fun i => Gr.zreq i = true)).image Gr.zreqE

/-- The fixed table. -/
def romK : ℕ := ∑ E ∈ Gr.bexpSet, 3 ^ (Gr.sp * E)

theorem bexp_lt {E : ℕ} (hE : E ∈ Gr.bexpSet) : E < Gr.bmark + Gr.bz := by
  have hm : Gr.bmark = 3 ^ (Gr.n - 1) := rfl
  have hbs := Gr.bs_high
  have hbz := Gr.bz_high
  unfold bexpSet at hE
  rcases Finset.mem_union.1 hE with h | h
  · rcases Finset.mem_union.1 h with h' | h'
    · rcases Finset.mem_union.1 h' with h'' | h''
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h''
        have := Gr.edgeE_le hp
        omega
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h''
        have := Gr.markE_lt (Finset.mem_range.1 hi)
        omega
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h'
      have := (Gr.sgnE_bounds (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)).2
      omega
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
    exact (Gr.zreqE_bounds (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)).2

/-- **The table as a sum of distinct powers.**  Scaling the block exponents by the spacing
keeps them distinct. -/
theorem romK_eq_image : Gr.romK = ∑ e ∈ Gr.bexpSet.image (fun E => Gr.sp * E), 3 ^ e := by
  unfold romK
  rw [Finset.sum_image]
  intro E _ E' _ h
  have hsp : 0 < Gr.sp := by have := Gr.sp_ge; omega
  exact Nat.eq_of_mul_eq_mul_left hsp h

/-- **The table is a Boolean ternary numeral**, with nonzero digits only at multiples of the
spacing. -/
theorem dg_romK (p : ℕ) :
    dg Gr.romK p = if p ∈ Gr.bexpSet.image (fun E => Gr.sp * E) then 1 else 0 := by
  rw [Gr.romK_eq_image]
  exact Ternary.dg_sum_pow _ p

theorem romK_bool : Bool3 Gr.romK := by
  rw [Gr.romK_eq_image]
  exact Ternary.bool3_sum_pow _

end Graph

end Jones1980
