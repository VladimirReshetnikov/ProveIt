# Internal halting equivalence from represented Rotation240 entries

[`ArithmeticControlSimulationRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticControlSimulationRotation240.lean)
proves that the exact packed control interpreter and the numeric binary
machine halt together from every pair in the represented whole-frame relation.
Both execution clocks range over an arbitrary IΣ₁ model. The relation excludes
invalid controls and keeps the complete register file, tape, spare count and
padding gap.

The proof instantiates the existing `ArithmeticPositiveSimulation254` theorem
with the six checked [instruction endpoints](arithmetic_site_rotation240.md).
Each nonhalting instruction supplies a positive binary clock and a related
next configuration. Σ₁ induction therefore reaches binary clocks at least as
large as any given internal time. Halt absorption and the live-frame invariant
give the reverse halting direction; no upper bound on instruction clocks or
first-exit assumption is required.

The [actual check](results/arithmetic-control-simulation-rotation240-verification.json)
passes six axiom probes and eight typed callers with zero warnings and only
standard axioms. Source and audit took 2.515 and 2.069 seconds. The new unit
uses default proof limits, one thread, 4,096 MiB and a shared 120-second limit.
Its exact closure has 701 project prerequisites. No dependency family was
rebuilt.

The imported generic transport theorem retains its earlier checked source
settings of recursion depth 8,192 and 4,000,000 heartbeats. Its historical
record lacks the newer pre-audit object capture and some resource fields;
the guard records that difference explicitly. The identical Cantor source
has two historical compiled objects; the selected current object and the
older generic check's object are both recorded without rewriting history.

The [publication record](results/arithmetic-control-simulation-rotation240-publication.json)
and [history](arithmetic-control-simulation-rotation240/history.json.gz) preserve
the actual source, audit, logs, guard and independent source/API review.
This theorem applies at arbitrary represented entries. The exact blank start
is supplied by the separate startup and blank-control composition; the final
PA consistency sentence is a further composition.

Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt retain the attribution
of the source machine, calculus and compiler framework.
