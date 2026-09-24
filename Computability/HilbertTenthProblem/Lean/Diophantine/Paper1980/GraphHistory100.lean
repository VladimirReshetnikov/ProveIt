import Diophantine.Paper1980.GraphCompiled100
import Diophantine.Paper1980.Counters100

/-!
# The serial run of the counter certificate

`EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md`, §1: *"At serial block b, the active register
is b modulo three.  The source state's sign updates that register by one, and z_i=1 requires
its source value to be zero.  Other registers wait for their own blocks.  Every supplied
counter value remains nonnegative.  The initial vector is [2x,0,0] ... The final vector is all
zero."*  And §6: *"This proves the exact serial labelled-counter relation of Section 1."*

`Graph.SerialRun` is that relation for a graph controller whose entry is state zero and whose
run is cyclic: a state sequence from the entry along permitted edges with an edge back to the
entry, and a block value sequence starting at `[2x, 0, 0]`, moving by the source state's sign
three blocks later, zero wherever the source state requests a zero test, and ending at zero
in all three registers.  The values are natural numbers, so they stay nonnegative.

In the Lean labels, `zreq i = true` is the *no-zero-request* label (the zero field's row is
set), so a zero test is requested exactly when `zreq i = false`.

`graph_serial_run100` reads every positive solution of `Sys100` over a graph controller's own
ROM as such a run: the decoded path supplies the states and the labels of the sign and zero
fields, and the counter history supplies the values.
-/

namespace Jones1980

open Ternary

/-- **An accepting serial run** of a graph controller on input `x`, with `u` blocks. -/
structure Graph.SerialRun (Gr : Graph) (x u : ℕ) (st val : ℕ → ℕ) : Prop where
  /-- At least one full register bank. -/
  three_le : 3 ≤ u
  /-- The run starts at the entry. -/
  start : st 0 = 0
  /-- Every block has a state. -/
  states : ∀ b, b < u → st b < Gr.n
  /-- Consecutive states are permitted edges. -/
  step : ∀ b, b + 1 < u → Gr.adj (st b) (st (b + 1)) = true
  /-- The last state returns to the entry. -/
  wrap : Gr.adj (st (u - 1)) 0 = true
  /-- The registers start at `[2x, 0, 0]`. -/
  init : val 0 = 2 * x ∧ val 1 = 0 ∧ val 2 = 0
  /-- The active register moves by the source state's sign. -/
  update : ∀ b, b < u →
    (val (b + 3) : ℤ) = val b + (if Gr.sgn (st b) = true then 1 else -1)
  /-- A zero-test state finds its register at zero. -/
  zero_test : ∀ b, b < u → Gr.zreq (st b) = false → val b = 0
  /-- All three registers end at zero. -/
  final : val u = 0 ∧ val (u + 1) = 0 ∧ val (u + 2) = 0

set_option maxHeartbeats 1000000 in
/-- **Every positive solution is an accepting serial run.**  Under the terminal convention,
every positive solution of `Sys100` over a graph controller's own compiled ROM has the radix
geometry, and its halved state, sign, zero and track fields form an accepting serial run of
the controller on the input `x`. -/
theorem graph_serial_run100 {Gr : Graph}
    (hconv : ∀ ii, ii < Gr.n → Gr.adj ii 0 = true → Gr.zreq ii = true)
    {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
    (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
    (hS : Sys100 (Gr.rom Gr.gridZon (3 ^ Gr.sp)) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a
      c d f h i j k o s w τ η ζ γ y) :
    ∃ e m u, Geometry100 H R q e m u ∧ ∃ st val : ℕ → ℕ, Gr.SerialRun x u st val := by
  have hOk := Gr.rom_grid_ok
  obtain ⟨e, m, u, hG⟩ := geometry100 hP hS hOk.Zon_ge hOk.B0_ge
  have hGrid := Gr.rom_port_grid
  have hDq := graph_decode_bound100 hOk hP hS hG hGrid hconv
  obtain ⟨pc, kp, dd, st, -, hKp, hD, hst0, hrows, hedges, hwrap⟩ :=
    graph_path100 hOk hP hS hG hGrid
  obtain ⟨a0, a1, kp', km, dd', -, -, hKp', -, hD', hsign, hbound, h0, h1, h2, hchain⟩ :=
    counter_history_rom100 hOk hP hS hG (Gr.rom_sidon _ _) (Gr.rom_layout _ _) hDq
  have hkk : kp' = kp := by omega
  have hdd : dd' = dd := by omega
  subst hkk hdd
  have hu3 := hG.hu
  -- rows past the top are empty
  have hddB : dd' < 3 ^ (m * u) := by
    have hSid := Gr.rom_sidon Gr.gridZon (3 ^ Gr.sp)
    have hdm := marker_lt_width hOk hP hS hG hSid
    obtain ⟨hDle, -⟩ :=
      nonneg_upper100 hOk hP hS hG hSid (le_of_lt hdm) (state_lt_width hOk hP hS hG hSid)
        (state_small hOk hP hS hG hSid) hOk.I_pos (code_small hOk hP hS hG hSid)
        (route_residue100 hOk hP hS hG hSid)
        (exponent_layout100 hOk hP hS hG hSid (Gr.rom_layout _ _))
    have hHh := hG.hH
    have := heads_lt m u hG.hm
    omega
  have hval0 : ∀ b, u ≤ b → row (a0 + a1) m b = 0 := by
    intro b hb
    have := hbound b
    rw [row_eq_zero_of_ge hddB hb, Nat.mul_zero] at this
    omega
  refine ⟨e, m, u, hG, st, fun b => row (a0 + a1) m b,
    { three_le := hu3
      start := hst0
      states := fun b hb => (hrows b hb).1
      step := hedges
      wrap := hwrap
      init := ⟨h0, h1, h2⟩
      update := fun b hb => ?_
      zero_test := fun b hb hz => ?_
      final := ⟨hval0 u le_rfl, hval0 (u + 1) (by omega), hval0 (u + 2) (by omega)⟩ }⟩
  · have hc := hchain (b + 3) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at hc
    have hs := hsign b hb
    have hk := (hrows b hb).2.2.1
    show (row (a0 + a1) m (b + 3) : ℤ) = row (a0 + a1) m b + _
    by_cases hsg : Gr.sgn (st b) = true
    · rw [if_pos hsg] at hk ⊢
      have hkm : row km m b = 0 := by omega
      rw [hk, hkm] at hc
      push_cast at hc
      linarith
    · rw [if_neg hsg] at hk ⊢
      have hkm : row km m b = 1 := by omega
      rw [hk, hkm] at hc
      push_cast at hc
      linarith
  · have hdz := (hrows b hb).2.2.2
    rw [if_neg (by rw [hz]; decide)] at hdz
    have := hbound b
    rw [hdz, Nat.mul_zero] at this
    show row (a0 + a1) m b = 0
    omega

end Jones1980
