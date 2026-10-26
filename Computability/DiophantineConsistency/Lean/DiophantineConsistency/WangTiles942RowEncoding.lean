import DiophantineConsistency.WangTiles942StripGeometry
import DiophantineConsistency.WangMachineEncoding

/-!
# The first machine configuration in the derived finite strip

Row encoding means actual north colors in the open interval and an
interior machine head. It asserts no transition or halting theorem.
The marked-word initialization theorem derives this encoding for the
actual machine after its first blank-tape step.
-/

namespace DiophantineConsistency.WangTiles942RowEncoding

open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Periodic WangTiles942InitialStrip
  WangTiles942StripGeometry

set_option Elab.async false

/-- Only colors inside the fixed strip are read. No assertion about an
exterior tape or future machine steps is part of this definition. -/
structure RowEncodes (T : ℤ → ℤ → Tile) (l r t : ℤ) (cfg : Config 215) : Prop where
  head_left : l < cfg.head
  head_right : cfg.head < r
  north : ∀ x : ℤ, l < x → x < r → (T x t).north = WangMachineEncoding.color cfg x

theorem RowEncodes.color_bound {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (h : RowEncodes T l r t cfg) (x : ℤ) (hl : l < x) (hr : x < r) :
    (T x t).north ≤ 433 := by
  rw [h.north x hl hr]
  exact WangMachineEncoding.color_le_433 cfg x

theorem RowEncodes.head_iff {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (h : RowEncodes T l r t cfg) (x : ℤ) (hl : l < x) (hr : x < r) :
    2 ≤ (T x t).north ↔ x = cfg.head := by
  rw [h.north x hl hr]
  exact WangMachineEncoding.head_iff cfg x

theorem RowEncodes.plain {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (h : RowEncodes T l r t cfg) (x : ℤ) (hl : l < x) (hr : x < r)
    (hx : x ≠ cfg.head) : (T x t).north = (Tape.read cfg.tape x).toNat := by
  rw [h.north x hl hr]
  exact WangMachineEncoding.color_of_ne_head cfg x hx

theorem RowEncodes.operating_head {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (h : RowEncodes T l r t cfg) (q : Fin 215) (hq : cfg.state = some q) :
    (T cfg.head t).north = WangTiles942.headColor q.val (Tape.read cfg.tape cfg.head).toNat := by
  rw [h.north cfg.head h.head_left h.head_right, WangMachineEncoding.color_at_head, hq]
  rfl

/-- Time matching transfers the derived seeded South row to the exact
initialized machine configuration on the next row. -/
theorem initialized_row {T : ℤ → ℤ → Tile} {N L R : ℕ}
    (h : InitialStrip (fun x => T x 0) N L R)
    (hTime : ∀ x : ℤ, (T x 1).north = (T x 0).south) :
    RowEncodes T (-(L : ℤ)) (R : ℤ) 1 DecimalMachineInitialization.initialized := by
  have hl := h.left_pos
  have hr := h.right_min
  refine ⟨by change -(L : ℤ) < 1; omega, by change (1 : ℤ) < R; omega, ?_⟩
  intro x hxl hxr
  rw [hTime x, initial_south h x hxl hxr, WangMachineEncoding.initialized_color]

/-- The initial configuration is the actual decimal machine at clock1,
not a separately supplied blank or seeded run. -/
theorem marked_initialized_strip {N : ℕ} [NeZero N] {s : ℤ} {a : ZMod N → Fin 942}
    (h : MarkedWord N s a) : ∃ L R : ℕ,
      PersistentStrip (plane N s a) N L R ∧
      RowEncodes (plane N s a) (-(L : ℤ)) (R : ℤ) 1
        (DecimalMachine215.machine.run 1) := by
  obtain ⟨L,R,hs⟩ := marked_persistent_strip h
  refine ⟨L,R,hs,?_⟩
  rw [DecimalMachineInitialization.run_one]
  exact initialized_row hs.initial (fun x => plane_time_matching h x 0)

end DiophantineConsistency.WangTiles942RowEncoding
