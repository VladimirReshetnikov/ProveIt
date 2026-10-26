# Persistent finite strip walls and a seam-free interior

Date: 2026-10-26. Author and full source/check reviewer: ROOT. This is an
author receipt, not an independent peer review.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942StripGeometry.lean (90 lines) | 2439e3e5bd3b9f4eeea38013e4a2e237444626cc5864b0244463be8a88ce4e7a |
| WangTiles942StripGeometryChecks.lean (42 lines) | 2c68d346ff2075c41fab3e96b1e106bd4034ac33300a5b779419a59aac7a8aaf |

Both complete sources were read before bounded execution. The first main
run passed with an unused final omega warning; that redundant tactic was
removed and the changed proof read before replay. Final main and the first
checks run both passed with `lake env lean -M6000 -j1`, asynchronous
elaboration disabled. The final main log is empty; all five axiom audits
contain only the standard axioms. The checks imported the main object
freshly generated from this final source. No full dependency or umbrella
rebuild is claimed.

`initial_tile` covers every integer strictly between-L andR by splitting
negative, zero, one and remaining positive positions. Natural-distance
indices are converted with explicit nonnegative integer cast equalities.
It retains all exact initializer tuples, including Start at0 and the true
head initializer at1. Both vertical colors differ from437 there, and
the South color is exactly1 at0,4 at1,0 everywhere else inside the strip.

`persistent_of_initial` needs only actual Allowed tiles, true time matching
and that initial strip. Seam-column invariance gives exact seam tuples at
both fixed walls for every integer time; the finite horizontal parameters
may change. At an interior coordinate, a future or past seam would imply
a seam at time0, contradicting its proved initial tile. Both north and
south color437 are excluded throughout the interior.

`marked_persistent_strip` starts from only the actual three-field MarkedWord
and derives its initial strip from horizontal periodicity. Thus its finite
walls and all-time seam-free interior are conclusions, not supplied
geometry. Focused checks retain the seeded South row, numerical bounds,
the two distinguished interior coordinates and arbitrary integer time.
No globally unique Start, rectangular quotient, machine run or halting
premise appears. Initialization-to-machine calibration and run extraction
remain subsequent work. The decimal equation and metrics are unchanged.
