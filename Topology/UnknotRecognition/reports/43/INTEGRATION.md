# Opt-in integration plan

Target: `Topology/UnknotRecognition`, commit
`04d799b69d388f75ce85539b26fca1585f9d2651`.
Suggested destination for this initial research package:
`Topology/UnknotRecognition/research/whitehead_exposure/`.
Keep the package self-contained until the production checks below are complete.

## Existing interfaces

The audited `group_certificate.py` has a private `_presentation(diagram,budget)`
returning `(alive, words)` and a `_Budget(check,max_letters,max_work)`.
Its ordinary Whitehead producer already uses signed-terminal minimum cuts.
Its elementary verifier accepts valid `whitehead` moves without requiring
negative length change. Version-1 `wirtinger-cyclic-group` certificates therefore
suffice for the new stage's output; no new inference rule is introduced.

`integration/fastunknot_adapter.py` reconstructs the full presentation, runs the
new stage, emits the existing format, and invokes the maintained verifier.
The bare `Diagram(...)` constructor is not itself validation; the adapter
revalidates with `Diagram.from_pd(diagram.pd)`. It never accepts arbitrary
presentation JSON as a topological certificate.

The stage stores at most M letters after each completed rank drop. Its
Whitehead workspace, and the independent literal replay allowance, are 3M.
Search and replay have separate work allowances; the wall-clock callback is
shared and polled. It is not a hard real-time or preemptive deadline.
Caller cancellation must propagate.

## Required checks before enabling a production option

Run the adapter smoke script with both this `src/` and the repository's `fast/`
on PYTHONPATH. Then run the full maintained suite. Import failure is a failure
to run, not a skip counted as a pass. Compare reconstructed initial presentations
and replay every positive certificate, especially after existing preprocessing.

Benchmark conclusive end-to-end outcomes with the proposed stage disabled and
enabled. Include hard unknots, ordinary nontrivial knots, the current stress
corpus, and the Gordian fixture. Record peak letters, peak compressed nodes,
flow work, certificate bytes, and total time including independent replay.
Preserve failed and timed-out cases. The supplied easy braid corpus showed no
coverage gain and slight aggregate overhead; it cannot justify default-on use.

The isolated strict comparator in this package has no relator-overlap moves
and does not emulate every production heuristic. It is a controlled comparator
for the mathematical separation, not a production baseline.

## Recommended scheduling experiment

Probe the new oracle on the current residual presentation after a bounded
existing group search stalls, rather than immediately discarding the residual
and restarting. Preserve every relation slot, active-generator name, original
input binding, prior elementary moves, and shared budget. A successful exposure
adds one ordinary Whitehead move and one elimination to that exact trace.
If it fails, continue the existing overlap or complete fallback branch.

This residual handoff is proposed, not implemented in the generic adapter.
Do not claim the rank-first greedy policy is complete just because a different
choice sequence might admit small rank drops.

## Known limits

The selector optimizes a raw allocation bound, not final reduced length or
future difficulty. Fused replay is a separate single-exposure small-image
verifier; it is not general compressed free reduction or a complete compressed
iterative search. The provided Gordian residual has no unit bridges, and the
presentation `<a,b | a^2,a^3>` proves that relator interaction can be essential.
