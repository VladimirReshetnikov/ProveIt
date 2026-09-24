import Diophantine.Paper1980.Decode100

/-!
# A compiled on-grid word

`ROM100.Grid` asks four things of the fixed program's grid numeral: the spacing is a power of
three, the numeral is a Boolean ternary word, it marks every target column and both port
columns, and it marks only grid positions.  `ROM100.Ok` asks that the same numeral exceed a
handful of fixed bounds.  This module builds one numeral that does both, so the grid layout
is not vacuous, just as `Controller.rom_ok` shows for the grid inequalities alone.

Take spacing `B₀ = 9`, so the grid positions are the even exponents.  Every target column
`d + a j = 3^(n−1) + 3^j` is even, being a sum of two odd numbers; the port columns
`d + bs` and `d + bz` are even once the port offsets are odd, which a compiler is free to
choose.  `gridZon` marks exactly those columns and one more, at twice the old grid numeral
`zonChoice`, which makes it large enough for every bound of `ROM100.Ok`.

`decoded_compiled100` is the payoff: for a compiled controller with odd port offsets and the
terminal convention, *every* positive solution of `Sys100` over its own ROM satisfies the
decoded-control bound, returns to the cyclic entry, and has the controller path as its state
field.  Nothing about the grid is assumed any more.
-/

namespace Jones1980

open Ternary Finset

namespace Controller

variable (P : Controller)

/-- The columns the compiled grid numeral marks: every target column, both port columns,
and one high column that makes the numeral large. -/
def gridSet : Finset ℕ :=
  (range P.n).image (fun j => P.mark + coord j) ∪
    {P.mark + P.bs, P.mark + P.bz, 2 * P.zonChoice}

/-- The compiled grid numeral. -/
def gridZon : ℕ := ∑ e ∈ P.gridSet, 3 ^ e

theorem zonChoice_lt_gridZon : P.zonChoice < P.gridZon := by
  have h1 : 3 ^ (2 * P.zonChoice) ≤ P.gridZon :=
    Finset.single_le_sum (f := fun e => 3 ^ e) (fun _ _ => Nat.zero_le _)
      (Finset.mem_union_right _ (by simp))
  have h2 : P.zonChoice < 3 ^ P.zonChoice := Ternary.lt_three_pow _
  have h3 : (3 : ℕ) ^ P.zonChoice ≤ 3 ^ (2 * P.zonChoice) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **The compiled grid numeral meets the fixed grid inequalities.** -/
theorem rom_grid_ok : (P.rom P.gridZon 9).Ok where
  B0_ge := le_refl 9
  Zon_ge := by
    have h1 : 81 ≤ P.zonChoice := P.rom_ok.Zon_ge
    have h2 := P.zonChoice_lt_gridZon
    show 81 ≤ P.gridZon
    omega
  Zon_gt_S := by
    have h1 : 4 * P.romS < P.zonChoice := P.rom_ok.Zon_gt_S
    have h2 := P.zonChoice_lt_gridZon
    show 4 * P.romS < P.gridZon
    omega
  Zon_gt_gI := by
    have h1 : P.romg * (3 ^ coord 0 + 1) < P.zonChoice := P.rom_ok.Zon_gt_gI
    have h2 := P.zonChoice_lt_gridZon
    show P.romg * (3 ^ coord 0 + 1) < P.gridZon
    omega
  Zon_gt_KgS := by
    have h1 : (P.romK + P.romg) * (P.romS + 1) < P.zonChoice := P.rom_ok.Zon_gt_KgS
    have h2 := P.zonChoice_lt_gridZon
    show (P.romK + P.romg) * (P.romS + 1) < P.gridZon
    omega
  S_pos := P.romS_pos
  I_pos := by show (0 : ℕ) < 3 ^ coord 0; positivity
  g_pow := ⟨P.mark, rfl⟩
  K_lt_hz := P.romK_lt_hz
  Zon_gt_ports := by
    have h1 : 8 * (P.romhs + P.romhz) < P.zonChoice := P.rom_ok.Zon_gt_ports
    have h2 := P.zonChoice_lt_gridZon
    show 8 * (P.romhs + P.romhz) < P.gridZon
    omega
  K_pos := P.romK_pos

theorem mark_odd : P.mark % 2 = 1 := by
  show 3 ^ (P.n - 1) % 2 = 1
  rw [Nat.pow_mod]
  norm_num

/-- **The compiled grid numeral has the grid layout**, once the port offsets are odd. -/
theorem rom_grid_layout (hbs : P.bs % 2 = 1) (hbz : P.bz % 2 = 1) :
    (P.rom P.gridZon 9).Grid P 2 where
  spacing := by show (9 : ℕ) = 3 ^ 2; norm_num
  lg_pos := by norm_num
  bool_Zon := by
    show Bool3 (∑ e ∈ P.gridSet, 3 ^ e)
    exact Ternary.bool3_sum_pow _
  marks_targets := fun j hj => by
    show dg (∑ e ∈ P.gridSet, 3 ^ e) (P.mark + coord j) = 1
    have hmem : P.mark + coord j ∈ P.gridSet :=
      Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩)
    rw [Ternary.dg_sum_pow, if_pos hmem]
  marks_sgn := by
    show dg (∑ e ∈ P.gridSet, 3 ^ e) (P.mark + P.bs) = 1
    have hmem : P.mark + P.bs ∈ P.gridSet := Finset.mem_union_right _ (by simp)
    rw [Ternary.dg_sum_pow, if_pos hmem]
  marks_zreq := by
    show dg (∑ e ∈ P.gridSet, 3 ^ e) (P.mark + P.bz) = 1
    have hmem : P.mark + P.bz ∈ P.gridSet := Finset.mem_union_right _ (by simp)
    rw [Ternary.dg_sum_pow, if_pos hmem]
  on_grid := fun p hp => by
    have hp' : dg (∑ e ∈ P.gridSet, 3 ^ e) p = 1 := hp
    have hmem : p ∈ P.gridSet := by
      by_contra hc
      rw [Ternary.dg_sum_pow, if_neg hc] at hp'
      omega
    have hm2 := P.mark_odd
    rcases Finset.mem_union.1 hmem with h | h
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      have hc2 : coord j % 2 = 1 := by
        show 3 ^ j % 2 = 1
        rw [Nat.pow_mod]
        norm_num
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl <;> omega

end Controller

/-- **The decoded controller of a compiled program.**  For a compiled controller with odd
port offsets and the terminal convention, every positive solution of `Sys100` over its own
ROM has the radix geometry, satisfies the decoded-control bound, returns to the cyclic entry
after its full height, and has the controller path as its state field.  Every hypothesis
about the fixed ROM is now supplied by the compilation. -/
theorem decoded_compiled100 {P : Controller} (hbs : P.bs % 2 = 1) (hbz : P.bz % 2 = 1)
    (hconv : ∀ ii, ii < P.n → P.f ii = 0 → P.zreq ii = true)
    {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
    (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
    (hS : Sys100 (P.rom P.gridZon 9) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i
      j k o s w τ η ζ γ y) :
    ∃ e m u, Geometry100 H R q e m u ∧ 2 * q ≤ R * D ∧ P.f^[u] 0 = 0 ∧
      ∃ pc, PC = 2 * pc ∧ ∀ ii, ii < u → row pc m ii = 3 ^ coord (P.f^[ii] 0) := by
  have hOk := P.rom_grid_ok
  obtain ⟨e, m, u, hG⟩ := geometry100 hP hS hOk.Zon_ge hOk.B0_ge
  exact ⟨e, m, u, hG,
    decoded_controller100 hOk hP hS hG (P.rom_grid_layout hbs hbz) hconv⟩

end Jones1980
