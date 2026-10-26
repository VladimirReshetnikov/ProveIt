import DiophantineConsistency.WangTiles942RowStep

/-! Focused composition checks for actual row evolution, including entry
into halt, the original destination bit, the marked plane and clock1. -/

namespace DiophantineConsistency.WangTiles942RowStepChecks

open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Language WangTiles942Periodic
  WangTiles942StripGeometry WangTiles942RowEncoding WangTiles942RowStep

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

variable {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}

-- The endpoint takes only the original matching/geometry/encoded-row
-- data and a live state. No no-finish or clean-row premise is introduced.
example (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    RowEncodes T (-(L : ℤ)) (R : ℤ) (t+1) (DecimalMachine215.machine.step cfg) :=
  row_step hA hH hTime hs hrow q hq

-- An actual halting action still moves and uses the old destination bit.
theorem entering_halt_north (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (hh : (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).next = none) :
    let p := (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).move.apply cfg.head
    (T p (t+1)).north = 432 + (Tape.read cfg.tape p).toNat := by
  dsimp only
  have hb := WangTiles942HeadBounds.next_head_inside hA hH hs hrow q hq
  have he : (DecimalMachine215.machine.step cfg).head =
      (DecimalMachine215.machine.transition q
        (Tape.read cfg.tape cfg.head)).move.apply cfg.head := by
    rw [WangMachineStep.step_eq _ cfg q hq]
  rw [he] at hb
  rw [hTime]
  have hc := receiver_south hA hH hrow q hq _ hb.1 hb.2 rfl
  rw [hh, WangMachineEncoding.halted_head_color] at hc
  exact hc

theorem marked_row_step {s : ℤ} {a : ZMod N → Fin 942} [NeZero N]
    (h : MarkedWord N s a) (hs : PersistentStrip (plane N s a) N L R)
    (hrow : RowEncodes (plane N s a) (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    RowEncodes (plane N s a) (-(L : ℤ)) (R : ℤ) (t+1)
      (DecimalMachine215.machine.step cfg) :=
  row_step (plane_allowed N s a) (plane_east_matching h) (plane_time_matching h)
    hs hrow q hq

-- Clock1 comes from the literal initialized row, then the actual machine
-- step reaches clock2. Neither encoding is supplied as a new premise.
theorem marked_second_row {s : ℤ} {a : ZMod N → Fin 942} [NeZero N]
    (h : MarkedWord N s a) : ∃ L R : ℕ,
    PersistentStrip (plane N s a) N L R ∧
    RowEncodes (plane N s a) (-(L : ℤ)) (R : ℤ) 2
      (DecimalMachine215.machine.step (DecimalMachine215.machine.run 1)) := by
  obtain ⟨L,R,hs,hi⟩ := marked_initialized_strip h
  have hq : (DecimalMachine215.machine.run 1).state = some (1 : Fin 215) := by
    rw [DecimalMachineInitialization.run_one]
    rfl
  exact ⟨L,R,hs,marked_row_step h hs hi 1 hq⟩

#print axioms head_south
#print axioms far_west_zero
#print axioms far_east_zero
#print axioms far_pass
#print axioms receiver_south
#print axioms south_step
#print axioms row_step
#print axioms entering_halt_north
#print axioms marked_row_step
#print axioms marked_second_row

end DiophantineConsistency.WangTiles942RowStepChecks
