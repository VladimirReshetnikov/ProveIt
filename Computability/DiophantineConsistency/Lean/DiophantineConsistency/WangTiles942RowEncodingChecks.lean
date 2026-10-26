import DiophantineConsistency.WangTiles942RowEncoding

namespace DiophantineConsistency.WangTiles942RowEncodingChecks

open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Periodic WangTiles942StripGeometry WangTiles942RowEncoding

set_option Elab.async false

/-- The two color regimes recover head uniqueness within the interval. -/
example {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (h : RowEncodes T l r t cfg) (x : ℤ) (hl : l < x) (hr : x < r)
    (hx : x ≠ cfg.head) : (T x t).north ≤ 1 ∧ (T cfg.head t).north ≥ 2 := by
  refine ⟨?_, (h.head_iff cfg.head h.head_left h.head_right).mpr rfl⟩
  rw [h.north x hl hr]
  exact WangMachineEncoding.plain_color_le_one cfg x hx

/-- Every encoded row excludes the Start boundary input at every interior
position, including at a halted head. This is a later periodicity obstruction. -/
example {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (h : RowEncodes T l r t cfg) (x : ℤ) (hl : l < x) (hr : x < r) :
    (T x t).north ≠ 435 := by
  have hh := h.color_bound x hl hr
  omega

/-- MarkedWord alone supplies geometry and the exact actual clock1 row;
no initialization or run correspondence is a premise. -/
example {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}
    (h : MarkedWord N s a) : ∃ L R : ℕ,
      PersistentStrip (plane N s a) N L R ∧
      RowEncodes (plane N s a) (-(L : ℤ)) (R : ℤ) 1
        (DecimalMachine215.machine.run 1) := marked_initialized_strip h

#print axioms RowEncodes.color_bound
#print axioms RowEncodes.head_iff
#print axioms RowEncodes.plain
#print axioms RowEncodes.operating_head
#print axioms initialized_row
#print axioms marked_initialized_strip

end DiophantineConsistency.WangTiles942RowEncodingChecks
