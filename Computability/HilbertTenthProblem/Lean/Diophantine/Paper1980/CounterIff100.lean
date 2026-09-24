import Diophantine.Paper1980.WitnessRun100

/-!
# The 100-operation certificate decides three-counter acceptance

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §6: *"This proves both directions for the same
compiled ordinary-input predicate with 100 operations."*

For every three-counter program `M` and every positive input `x`, the program accepts `x`
exactly when the 100-operation system over the compiled ROM of `M` has a positive solution at
`x`:

* a positive solution is an accepting serial run of the compiled graph
  (`graph_serial_run100`), which is an accepting computation of `M` (`accepts_of_run`);
* an accepting computation is laid out as an accepting serial run of even length
  (`run_of_accepts`), whose canonical witness is a positive solution (`solvable_of_run`).

The compiled graph's first bank is all-plus, and its terminal convention holds
(`CProgram.graph_conv`).  What is left for universality is §§1–3 of the compiler note: a
program accepting exactly the members of a given recursively enumerable set.
-/

namespace Jones1980

theorem CProgram.graph_sgn0 (M : CProgram) : M.graph.sgn 0 = true := by
  show M.sgnSL (0 / 3) (0 % 3) = true
  unfold CProgram.sgnSL
  simp

/-- **Acceptance by a three-counter program is 100-operation Diophantine.** -/
theorem accepts_iff_solvable100 (M : CProgram) {x : ℕ} (hx : 0 < x) :
    M.Accepts x ↔ Solvable100 (M.graph.rom M.graph.gridZon (3 ^ M.graph.sp)) x := by
  constructor
  · intro h
    obtain ⟨u, st, val, hu, hrun⟩ := M.run_of_accepts h
    exact solvable_of_run hrun hx M.graph_conv M.graph_sgn0 hu
  · rintro ⟨q, J, W, H, v, t, A0, A1, Kp, Km, D, α, R, PC, PV, β, z, r, a, c, d, f, h, i, j, k,
      o, s, w, τ, η, ζ, γ, y, hP, hS⟩
    exact accepts_of_sys100 hP hS

end Jones1980
