# ArithmeticSite215 — author construction and replay

27 October 2026. PASS. controller_certificate authored and fully reviewed
the final 185-line main and 76-line Checks, then completed a fresh capped
private replay. Independent review is pending. Only these two new Lean
leaves and their new evidence were written; no accepted source, shared
object, shared progress document or Git state was changed.

The exact imports are ArithmeticHome215 and KSites215. The former is the
accepted actual arithmetic executor; the latter supplies the complete
literal source certificate for 4,751 leaves in 105 kernel blocks. This
packet does not rerun those closed certificates or use KSim's ordinary-Nat
runTo_sound, sim_step or halts_iff as an internal premise.

## Uniform execution and exact data

All execution statements quantify over arbitrary ORing models of IΣ1.
The gap, nine register values, positive spare count and clocks are internal,
including nonstandard values. Paths, source operations and fuel 4000 remain
finite syntax. There is no positive-gap or positive-register hypothesis.

source_checked obtains every actual checkEdge result from LeafAt and the
closed all_sites theorem. It derives path length at most 48, excludes node
operations and derives both the logical and physical register bounds.
The literal nine-entry physical map is kernel checked. No source endpoint
assumes that its site checker or desired execution succeeds.

runTo_actual extracts the actual executor result and applies accepted
Home.exec_matches_actual. runHalt_actual applies Home.exec_actual and
halt_interpret. Both begin with moved=false and therefore retain a positive
execution clock, even if individual scans or normalization steps are empty.
Halt is first(configuration)=0 at sparse state 230, in either tape-facing
orientation. The full terminal payload, final write and move are retained;
scalar configuration equality to zero is not asserted.

The six LeafAt clients cover INC, DEC zero, DEC positive, break, continue
and halt. DEC assumptions are only the appropriate internal physical
register value branch. Their literal KSim target paths, overflow bits and
growth are unchanged. The source certificate establishes the physical
index bounds, so the total box interpretation's fallback is irrelevant.

start_format and target_format expose the complete numeric path, exact
distance, marker and register suffix. increment_target updates only the
selected register and appends a spare one. decrement_target updates only
the selected register, keeps the spare count and retains the extra distance
cell. These are algebraic full-tape identities, not canonical rebasing.

Checks include all nine physical bounds, both DEC branches at gap zero and
one spare, arbitrary internal values/clocks, whole payload updates and the
terminal state's preserved second projection. A concrete nonvacuous client
constructs the actual first leaf [false,false,false], DEC logical register 8
(physical 1), and executes it with zero gap, one spare and only v 1=0.

All 19 reports use standard Lean axioms only: physical_lt uses propext;
the five other finite source/bound reports use propext and Quot.sound;
the thirteen arithmetic reports use propext, Classical.choice and
Quot.sound. No sorry, native_decide, new axiom or cap increase occurs.

## Reproducible cache and attempts

The accepted plan SHA is
a2475b3256c6bdaf2cdcc25aafc7394500ab0fcdd9ae4cfdd12568096306530b,
with eleven-file manifest
29cde1cf02713dd1a8f092ec431c5de6117722a5252cff4c2dd9c36cdbc325ca.
Exact scope: 173 cached modules, including 95 Foundation modules, 458
custom artifacts, 41 boundary primaries plus 123 companions and 622 first
providers; zero dependency refresh. Accepted ROOT Home is selected from
/tmp/home215-root-gwo_lm6e/lib. The inherited source-identical, byte-unequal
KZip alternative remains explicitly recorded; the accepted current object
is retained. No Foundation or broad prerequisite build is performed.

The complete 115-line executed driver was read before execution and remains
unchanged across both attempts. It authenticates current source headers,
the reachable DAG, all pinned sources/artifacts and first providers on a
private package-only LEAN_PATH. Immutable inventory references replace a
duplicated full profile. Both input snapshots precede each attempt's first
compiler command. Fresh outputs are regular files, with pinned Lean 4.32,
-M6000 -j1 -DElab.async=false, one thread and 512MiB guards before and after
each invocation. No dependency is compiled.

Attempt 1 failed on a combined namespace-opening syntax, an explicit
startValue unfolding needed by rewrite, and one unused simp argument.
The fixes change no theorem statement or dependency. Attempt 2 passed both
leaves cleanly in 3.255 and 2.788 seconds. Main diagnostics are empty and
Checks has exactly the intended 19 reports. All two attempts, three
compiler invocations, four input snapshots, failures, commands, timings,
logs and available objects are pinned. Durable evidence copies are regular
hardlinks of immutable terminal files; no original evidence was removed.
The final driver reauthenticated 3020 observations across 1089 paths.

Final provider: /tmp/site215-controller-author-17ufgvs_/lib.

Source SHA256:

- Main: 9c3d64a9bba705e46ad8126e99cf92fef440b6514103ab5edda27f3689cd1bc3
- Checks: ca6f965e148fac20024ab04354fb9b74e7a840990a3e325131700641f1cab4ab

Object SHA256:

- Main: 1153b5306065169e5d3c9e758d4cb382c20fdcf0a3dccf522e7a82a44f8a1f81
- Checks: 0c1c83c656fe15550717abcb5ba97a494a38b7492bdb487d587b7732a0153d2d

I also authored Home, Symbolic, Boxes, Tape and earlier runtime dependencies.
This is an author receipt, not independent review of those prerequisites.
Canonical consumed-path rebasing, represented global frames, packed control
calibration, whole control/tape equivalence and its boot composition remain
later checkpoints. Source-ZFC calibration, internal polynomial/Pell witness
equivalence and the final HA proof-existence theorem remain open.

Evidence: [replay](arithmetic-site215-replay.json) and
[complete manifest](arithmetic-site215-author-replay/FILES.json).
Replay SHA256: 7ec6e9bf58d44960bd1d60a0f364229ce7a6f31d85f749c3e1a45a0484acdad9.
