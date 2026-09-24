import Diophantine.Paper1980.GraphCount100

/-!
# The graph router's ROM

The fixed numerals a compiled nondeterministic controller supplies to the counter system:

    S = Σ_i 3^(sp·3^i),   g = 3^(sp·bmark),   I = 3^(sp·3^0),
    hs = 3^(sp(bmark + bs)),   hz = 3^(sp(bmark + bz)),   K = the table.

As for the deterministic controller, the table is `1`-led at zero, because the marker term of
the last state has block exponent `bmark − bmark = 0` and every other exponent is positive, so
the Sidon and state-column layouts of the counter decoding hold automatically.

`PortGrid` is the grid layout the nondeterministic router needs.  Unlike the deterministic
one it does *not* ask the junk to avoid the target columns: unchosen edges stay in the junk
there.  It asks only that the on-grid word be Boolean, lie on the spacing grid, and mark the
two port columns.
-/

namespace Jones1980

open Ternary Finset

namespace Graph

variable (Gr : Graph)

/-- The marker numeral. -/
def romg : ℕ := 3 ^ (Gr.sp * Gr.bmark)

/-- The sign port. -/
def romhs : ℕ := 3 ^ (Gr.sp * (Gr.bmark + Gr.bs))

/-- The zero-request port. -/
def romhz : ℕ := 3 ^ (Gr.sp * (Gr.bmark + Gr.bz))

/-- The cyclic entry code, the entry being state zero. -/
def romI : ℕ := 3 ^ (Gr.sp * coord 0)

/-- The compiled ROM over a choice of grid numeral and spacing. -/
def rom (Zon B0 : ℕ) : ROM100 :=
  { Zon := Zon, B0 := B0, K := Gr.romK, g := Gr.romg, I := Gr.romI,
    hs := Gr.romhs, hz := Gr.romhz, S := Gr.romS }

theorem zero_mem_bexp : 0 ∈ Gr.bexpSet := by
  have hn : Gr.n - 1 < Gr.n := by have := Gr.two_le; omega
  have h := Gr.marker_mem hn
  have hc : coord (Gr.n - 1) = Gr.bmark := rfl
  rwa [hc, Nat.sub_self] at h

theorem romK_mod : Gr.romK % 3 = 1 := by
  rw [← Ternary.dg_zero_pos, Gr.dg_romK, if_pos]
  exact Finset.mem_image.2 ⟨0, Gr.zero_mem_bexp, Nat.mul_zero _⟩

theorem romK_lead : Ternary.Lead 0 1 Gr.romK :=
  ⟨Gr.romK, by rw [pow_zero, one_mul], Gr.romK_mod⟩

/-- The compiled ROM has the Sidon layout. -/
theorem rom_sidon (Zon B0 : ℕ) : (Gr.rom Zon B0).Sidon (Gr.sp * Gr.bmark) 0 where
  g_eq := rfl
  hs_eq := ⟨Gr.sp * Gr.bs, by show 3 ^ (Gr.sp * (Gr.bmark + Gr.bs)) = _; rw [Nat.mul_add]⟩
  hz_eq := ⟨Gr.sp * Gr.bz, by show 3 ^ (Gr.sp * (Gr.bmark + Gr.bz)) = _; rw [Nat.mul_add]⟩
  K_lead := Gr.romK_lead

/-- And the state-column layout, with the entry at the smallest column `sp`. -/
theorem rom_layout (Zon B0 : ℕ) :
    (Gr.rom Zon B0).Layout (Gr.sp * Gr.bmark) 0 Gr.sp (Gr.sp * Gr.bmark) where
  I_eq := by show 3 ^ (Gr.sp * coord 0) = 3 ^ Gr.sp; simp [coord]
  pK_eq := by omega
  amin_lt := by
    have h1 := Gr.three_le_bmark
    have h2 := Gr.sp_ge
    nlinarith
  amax_le := le_refl _

end Graph

/-- The grid layout of the nondeterministic router: the spacing is the graph's, the on-grid
word is Boolean, lies on the spacing grid, and marks both port columns. -/
structure Graph.PortGrid (Gr : Graph) (Cr : ROM100) : Prop where
  /-- The grid spacing. -/
  spacing : Cr.B0 = 3 ^ Gr.sp
  /-- The on-grid word is Boolean. -/
  bool_Zon : Bool3 Cr.Zon
  /-- The sign port column is on-grid. -/
  marks_sgn : dg Cr.Zon (Gr.sp * (Gr.bmark + Gr.bs)) = 1
  /-- The zero-request port column is on-grid. -/
  marks_zreq : dg Cr.Zon (Gr.sp * (Gr.bmark + Gr.bz)) = 1
  /-- The on-grid word marks only multiples of the spacing. -/
  on_grid : ∀ p, dg Cr.Zon p = 1 → p % Gr.sp = 0

end Jones1980
