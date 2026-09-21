/-!
# Probes for the pinned surreal-number implementation

Status: NOT executed during preparation of this archive. These probes reflect
source inspection, not a successful compilation report.

Repository: https://github.com/vihdzp/combinatorial-games
Revision: 02b4a908ea2ecfefffecb438f691951a814a5264
Lean: leanprover/lean4:v4.35.0-rc2
Mathlib: dec5b2b780537b6eaf7f5e5f000c12f7387fb24d

These probes intentionally do not claim an `IsRealClosed Surreal` instance,
a normal-form equivalence, or any analytic implementation. Locate and inspect
those declarations separately before depending on them.
-/

import CombinatorialGames.Surreal.Division
import CombinatorialGames.Surreal.HahnSeries.Basic

set_option pp.universes true

#check Surreal
#check SurrealHahnSeries
#check SurrealHahnSeries.mk
#synth Field Surreal.{0}
#synth Field SurrealHahnSeries.{0}
#check Surreal.mk_eq_mk
#print axioms Surreal.mk_eq_mk
