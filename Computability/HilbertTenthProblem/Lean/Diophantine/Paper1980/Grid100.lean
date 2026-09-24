import Diophantine.Paper1980.OneHot100

/-!
# The fixed grid and its complement

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §1, equation `(B₀ − 1)(Zon + z) = R − 1`, read
with the grid parameterization of `EXPLORATION_MERGED_PROGRAM_EMPTY_GRAPH.md`: the spacing
is `B₀ = 3^ℓ`, the on-grid threshold `Zon` is itself a power of three sitting at a grid
position, and the width coordinate is `z = (R − 1)/(B₀ − 1) − Zon`.

So the width equation says exactly that the threshold and the width coordinate add to the
**grid word** `heads ℓ t`, a `1` at every multiple of `ℓ` below the row width `R = 3^(ℓ t)`.
`grid_word` is that reading.  `grid_complement` then identifies the width coordinate: with
the threshold at grid position `k₀`, it is the grid word with that one position deleted,
and `bool3_grid_complement` says it is a Boolean ternary numeral.

This is what the junk pair of §5 needs.  Halving that pair gives two Boolean words summing
to `z · (H/2)`, so each row of the halved junk field is a sub-word of `z`: the junk is
supported on the grid positions other than the threshold's.  Combined with
`Ternary.dg_le_of_add` this is the exact support test the routing note performs with its
`TestV` field.
-/

namespace Jones1980

open Ternary

/-- Splitting the grid word at a row. -/
theorem heads_split {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∀ {t k : ℕ}, k ≤ t → heads ℓ t = heads ℓ k + 3 ^ (ℓ * k) * heads ℓ (t - k) := by
  intro t k
  induction k with
  | zero => intro _; simp [heads_zero]
  | succ k ih =>
    intro hk
    have hk' : k ≤ t := by omega
    have hsplit := ih hk'
    have hpeel : heads ℓ (t - k) = 1 + 3 ^ ℓ * heads ℓ (t - k - 1) := by
      conv_lhs => rw [show t - k = (t - k - 1) + 1 by omega]
      exact heads_succ' ℓ (t - k - 1)
    have hsucc : heads ℓ (k + 1) = heads ℓ k + 3 ^ (ℓ * k) := heads_succ ℓ k
    have hpow : (3 : ℕ) ^ (ℓ * (k + 1)) = 3 ^ (ℓ * k) * 3 ^ ℓ := by
      rw [show ℓ * (k + 1) = ℓ * k + ℓ from by ring, pow_add]
    have harg : t - (k + 1) = t - k - 1 := by omega
    rw [hsplit, hpeel, hsucc, hpow, harg]
    ring

/-- The grid word is Boolean. -/
theorem bool3_heads {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (t : ℕ) : Bool3 (heads ℓ t) := by
  intro p
  rw [dg_heads hℓ]
  split <;> omega

/-- **The width equation is the grid word.**  With spacing `B₀ = 3^ℓ` and row width
`R = 3^(ℓ t)`, the on-grid threshold and the width coordinate add to `heads ℓ t`. -/
theorem grid_word {B0 Zon z R ℓ t : ℕ} (hℓ : 1 ≤ ℓ) (hB0 : B0 = 3 ^ ℓ)
    (hR : R = 3 ^ (ℓ * t)) (h : (B0 - 1) * (Zon + z) + 1 = R) : Zon + z = heads ℓ t := by
  subst hB0
  subst hR
  have hgeo := heads_mul_sub_one ℓ t
  have hpos : 0 < (3 : ℕ) ^ ℓ - 1 := by
    have h1 : (3 : ℕ) ^ 1 ≤ 3 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
    omega
  have hcomm : ((3 : ℕ) ^ ℓ - 1) * (Zon + z) = (Zon + z) * (3 ^ ℓ - 1) := Nat.mul_comm _ _
  have hmul : (Zon + z) * (3 ^ ℓ - 1) = heads ℓ t * (3 ^ ℓ - 1) := by omega
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- **The width coordinate is the grid word with one position deleted.** -/
theorem grid_complement {Zon z ℓ t k0 : ℕ} (hℓ : 1 ≤ ℓ) (hk : k0 < t)
    (hZon : Zon = 3 ^ (ℓ * k0)) (h : Zon + z = heads ℓ t) :
    z = heads ℓ k0 + 3 ^ (ℓ * (k0 + 1)) * heads ℓ (t - k0 - 1) := by
  have hsplit := heads_split hℓ (le_of_lt hk)
  have hpeel : heads ℓ (t - k0) = 1 + 3 ^ ℓ * heads ℓ (t - k0 - 1) := by
    conv_lhs => rw [show t - k0 = (t - k0 - 1) + 1 by omega]
    exact heads_succ' ℓ (t - k0 - 1)
  have hpow : (3 : ℕ) ^ (ℓ * (k0 + 1)) = 3 ^ (ℓ * k0) * 3 ^ ℓ := by
    rw [show ℓ * (k0 + 1) = ℓ * k0 + ℓ from by ring, pow_add]
  rw [hsplit, hpeel] at h
  rw [hZon] at h
  rw [hpow]
  have hx : (3 : ℕ) ^ (ℓ * k0) * (1 + 3 ^ ℓ * heads ℓ (t - k0 - 1))
      = 3 ^ (ℓ * k0) + 3 ^ (ℓ * k0) * 3 ^ ℓ * heads ℓ (t - k0 - 1) := by ring
  omega

/-- And it is a Boolean ternary numeral. -/
theorem bool3_grid_complement {Zon z ℓ t k0 : ℕ} (hℓ : 1 ≤ ℓ) (hk : k0 < t)
    (hZon : Zon = 3 ^ (ℓ * k0)) (h : Zon + z = heads ℓ t) : Bool3 z := by
  rw [grid_complement hℓ hk hZon h]
  refine Ternary.bool3_chunk_cons (bool3_heads hℓ k0) ?_ (bool3_heads hℓ _)
  calc heads ℓ k0 < 3 ^ (ℓ * k0) := heads_lt ℓ k0 hℓ
    _ ≤ 3 ^ (ℓ * (k0 + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- The digits of the width coordinate: a `1` at every grid position below the row width
except the threshold's own. -/
theorem dg_grid_complement {Zon z ℓ t k0 : ℕ} (hℓ : 1 ≤ ℓ) (hk : k0 < t)
    (hZon : Zon = 3 ^ (ℓ * k0)) (h : Zon + z = heads ℓ t) (p : ℕ) :
    dg z p = if p % ℓ = 0 ∧ p < ℓ * t ∧ p ≠ ℓ * k0 then 1 else 0 := by
  have hZ : Bool3 Zon := by
    rw [hZon]
    intro j
    rw [dg_pow]
    split <;> omega
  have hz : Bool3 z := bool3_grid_complement hℓ hk hZon h
  have hle : ∀ j, dg Zon j + dg z j ≤ 2 := fun j => by
    have := hZ j; have := hz j; omega
  have hZp : dg Zon p = if p = ℓ * k0 then 1 else 0 := by rw [hZon, dg_pow]
  have hHp : dg (heads ℓ t) p = if p % ℓ = 0 ∧ p < ℓ * t then 1 else 0 := dg_heads hℓ t p
  have hsum : dg Zon p + dg z p = dg (heads ℓ t) p := by
    rw [← h, Ternary.dg_add_of_le_two hle]
  rw [hZp, hHp] at hsum
  by_cases hp : p = ℓ * k0
  · have hmem : p % ℓ = 0 ∧ p < ℓ * t := by
      subst hp
      exact ⟨Nat.mul_mod_right ℓ k0, by nlinarith [hk, hℓ]⟩
    rw [if_pos hp, if_pos hmem] at hsum
    rw [if_neg (fun hc => hc.2.2 hp)]
    omega
  · rw [if_neg hp] at hsum
    by_cases hmem : p % ℓ = 0 ∧ p < ℓ * t
    · rw [if_pos hmem] at hsum
      rw [if_pos ⟨hmem.1, hmem.2, hp⟩]
      omega
    · rw [if_neg hmem] at hsum
      rw [if_neg (fun hc => hmem ⟨hc.1, hc.2.1⟩)]
      omega

/-! ### The global-grid complement support -/

/-- **The support test.**  If the on-grid word and the width coordinate are both Boolean and
add to the grid word, the width coordinate vanishes wherever the on-grid word marks.  This
is the disjointness the routing note obtains from its `TestV` field, and what the counter
note's junk pair supplies: the junk's rows are sub-words of the width coordinate, so the
junk avoids every on-grid column. -/
theorem dg_complement_eq_zero {Zon z ℓ t p : ℕ} (hℓ : 1 ≤ ℓ) (hZ : Bool3 Zon) (hz : Bool3 z)
    (h : Zon + z = heads ℓ t) (hp : dg Zon p = 1) : dg z p = 0 := by
  have hle : ∀ j, dg Zon j + dg z j ≤ 2 := fun j => by
    have h1 := hZ j; have h2 := hz j; omega
  have hsum : dg Zon p + dg z p = dg (heads ℓ t) p := by
    rw [← h, Ternary.dg_add_of_le_two hle]
  have hh := bool3_heads hℓ t p
  omega

/-- The width coordinate replicated once per row: its rows are the width coordinate itself,
doubled, as the counter note's junk pair has it. -/
theorem row_complement_grid {z m u i : ℕ} (hz : 2 * z < 3 ^ m) (hi : i < u) :
    row (2 * z * heads m u) m i = 2 * z := by
  have hsum : 2 * z * heads m u = rowsum (fun _ => 2 * z) m u := by
    unfold rowsum heads
    rw [Finset.mul_sum]
  rw [hsum]
  exact row_rowsum (fun _ => hz) u i hi

/-- **The junk avoids the on-grid columns.**  Halving the junk pair gives two Boolean words
summing to the width coordinate once per row, so each row of the halved junk is a sub-word
of the width coordinate, which vanishes on the on-grid columns. -/
theorem junk_avoids_grid {Zon z ℓ t m u i p V Vbar : ℕ} (hℓ : 1 ≤ ℓ)
    (hZ : Bool3 Zon) (hzb : Bool3 z) (hgrid : Zon + z = heads ℓ t)
    (hV : Bool3 V) (hVb : Bool3 Vbar) (hpair : V + Vbar = z * heads m u)
    (hzm : z < 3 ^ m) (hi : i < u) (hp : p < m) (hon : dg Zon p = 1) :
    dg V (m * i + p) = 0 := by
  have hrow : row (z * heads m u) m i = z := by
    have hsum : z * heads m u = rowsum (fun _ => z) m u := by
      unfold rowsum heads
      rw [Finset.mul_sum]
    rw [hsum]
    exact row_rowsum (fun _ => hzm) u i hi
  have hdom := Ternary.dg_le_of_add hV hVb hpair (m * i + p)
  have hsplit : dg (z * heads m u) (m * i + p) = dg (row (z * heads m u) m i) p :=
    (Ternary.dg_row _ i hp).symm
  rw [hsplit, hrow, dg_complement_eq_zero hℓ hZ hzb hgrid hon] at hdom
  omega

/-! ### The grid layout of a compiled program -/

/-- The grid layout: the spacing is `3^ℓ`, the on-grid word is Boolean, and it marks every
target column.  Like the Sidon and state-column layouts, this is a property of the fixed
compilation, not of a supplied witness. -/
structure ROM100.Grid (Cr : ROM100) (P : Controller) (lg : ℕ) : Prop where
  /-- The grid spacing is a power of three. -/
  spacing : Cr.B0 = 3 ^ lg
  /-- The spacing is nontrivial. -/
  lg_pos : 1 ≤ lg
  /-- The on-grid word is a Boolean ternary numeral. -/
  bool_Zon : Ternary.Bool3 Cr.Zon
  /-- Every target column is on-grid. -/
  marks_targets : ∀ j, j < P.n → Ternary.dg Cr.Zon (P.mark + coord j) = 1
  /-- The sign port column is on-grid. -/
  marks_sgn : Ternary.dg Cr.Zon (P.mark + P.bs) = 1
  /-- The zero-request port column is on-grid. -/
  marks_zreq : Ternary.dg Cr.Zon (P.mark + P.bz) = 1
  /-- The on-grid word marks only multiples of the spacing. -/
  on_grid : ∀ p, Ternary.dg Cr.Zon p = 1 → p % lg = 0

/-- **The junk side of the counter route vanishes at every target column.**  The junk field
avoids the on-grid columns, and the two port terms sit above every target column, so the
transport reads the target columns of `K C` against the shifted state word alone. -/
theorem route_junk_vanishes {P : Controller} {Zon z lg t m u i j PV PVbar Kp D : ℕ}
    (hlg : 1 ≤ lg) (hZ : Bool3 Zon) (hzb : Bool3 z) (hgrid : Zon + z = heads lg t)
    (hj : j < P.n) (hon : dg Zon (P.mark + coord j) = 1)
    (hPV : Bool3 PV) (hPVb : Bool3 PVbar) (hpair : PV + PVbar = z * heads m u)
    (hzm : z < 3 ^ m) (hi : i < u) (hspan : P.mark + coord j < m)
    (hKpfit : ∀ k, 3 ^ (P.mark + P.bs) * row Kp m k < 3 ^ m)
    (hKpb : Kp < 3 ^ (m * u))
    (hDfit : ∀ k, 3 ^ (P.mark + P.bz) * row D m k < 3 ^ m)
    (hDb : D < 3 ^ (m * u))
    (hle : ∀ p, dg PV p + dg (3 ^ (P.mark + P.bs) * Kp) p + dg (3 ^ (P.mark + P.bz) * D) p ≤ 2) :
    dg (PV + 3 ^ (P.mark + P.bs) * Kp + 3 ^ (P.mark + P.bz) * D)
      (m * i + (P.mark + coord j)) = 0 := by
  have hcj : coord j ≤ P.mark := P.coord_le_mark hj
  have hbs := P.bs_high
  have hbz := P.bz_high
  have hm : P.mark = 3 ^ (P.n - 1) := rfl
  have hlt1 : P.mark + coord j < P.mark + P.bs := by omega
  have hlt2 : P.mark + coord j < P.mark + P.bz := by omega
  rw [Ternary.dg_add3_of_le_two hle,
    junk_avoids_grid hlg hZ hzb hgrid hPV hPVb hpair hzm hi hspan hon,
    dg_port_row hKpfit hKpb hi hlt1 hspan, dg_port_row hDfit hDb hi hlt2 hspan]

end Jones1980
