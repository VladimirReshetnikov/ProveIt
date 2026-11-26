/-
Source-level integration example. This file was not built in a joint environment.
It is meant for a project that has built both Main from grh-lean and the Cryptids
module below with a shared Lean/Mathlib toolchain. Upstream pins differ:
grh-lean uses Lean 4.35.0; Cryptids uses Lean 4.35.0-rc4.

grh-lean commit: 72fead102f663d5c7a407964a13dc0cf9d977207
Cryptids commit: 30d3f611b16faeb13f4d8281204253d36e4fae01
Both pinned Mathlib versions have the same Git blob for the RiemannZeta.lean
file defining RiemannHypothesis: e95eeb3463f021e719c6318dc346dca28d9522b9.
-/
import Main
import Cryptids.Semantics.Riemann95

theorem riemann95_never_halts :
    ¬ ConjectureMachines.Halts ConjectureMachines.Riemann95.candidate := by
  intro halts
  exact (ConjectureMachines.Riemann95.Semantics.halts_candidate_iff_not_riemannHypothesis.mp
    halts) riemannHypothesis
