# K215: remove generated WF witnesses, not just rebatch them

## Result

The next genuine simplification is a **proved all-node completion fold** that
constructs well-formedness directly from the existing node table. The three
487-entry tables are deterministic derived data, not independent evidence.
Compute only break/continue summaries and use completion rank as height.
This can replace 1,461 supplied numbers and sixteen finite witness-check
batches with one generic construction theorem and its concrete evaluation.

This is a research recommendation with finite validation, **not a checked
Lean patch**. A new generic Lean evaluator and invariant proof remain to be
implemented and benchmarked. A monolithic old `wfCheck` is explicitly not the
recommendation; that has already encountered memory limits.

## What was actually checked

- Sources pinned to ProveIt `beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc`;
  fetched source bytes match their Git blob IDs in `SOURCE_PINS.json`.
- Parsed the actual Dag222/Dag219/DagDom/DagPerm tables without executing
  incoming code: 487 nodes, 974 edges, root 0.
- Derived DFS postorder with memoization and cycle detection. Numeric IDs
  are not assumed topologically sorted; no order certificate was supplied.
- Computed canonical `(H,B,C)` equals every entry of the three old arrays.
  Root summary is `(178,0,0)`. The rank-only version computes no maximum
  height and supplies valid existing WF inequalities; root rank is 261.
- All-node traversal used 1,859 jobs within the 1,948-job counting bound.
- Eleven negative controls, including an unreachable cycle and incorrect
  CAR/CDR scope consumption, were rejected. Four positive boundary cases
  were accepted.
- All 14,741 one/two-node graphs over the chosen 10/11-edge alphabets agree
  with an independent readiness-scan implementation. Every accepted graph
  satisfies the original finite WF inequalities with completion-rank height.

`python check_wellformedness.py` reproduces these results using only adjacent
`sources/`, including the normalized-lane KSource215Programs source. The
normalized source hash is in the result and its Git blob is pinned.
The owned script does not import or execute any fetched generator.

## Compare the strongest current baseline

There are two relevant source lanes at this pin:

- `k215-simplification-2/plain_source`: ordinary 2,240-entry certificate,
  70-module source closure, sixteen separate `KSource215WfCheckXX` modules.
- `k215-simplification/source_normalization`: normalized 1,426-entry
  certificate, 30-module source closure. Its `KSource215Programs.lean`
  already holds all sixteen private WF batches in one module.

Both retain identical 1,461 WF table entries and the same all-487-node
proposition. A fold removes redundant *data and local witness checks* in
either lane. It can remove sixteen standalone files relative to the first
lane; it does **not** remove sixteen modules relative to the stronger
normalized lane. Adding a generic checker module could leave module count
unchanged or increase it; do not sell source structure as measured speed.

## Exact limits and alternatives

- Existing structured-execution contracts cannot supply this WF proof for
  free. The four DAG definitions are numeric overrides, not certified
  builders. The maintained generator already computes the proposed scope
  recurrences in Python; the new work is proving the construction in Lean.
- A supplied topological order is a simpler fallback formalization, but
  reduces external witness entries from 1,461 to 487, not to zero. It still
  needs range, uniqueness, coverage, and child-before-parent checks.
- Only 261 nodes are root-reachable. Omitting the other 226 from the current
  checker would weaken the stated WF claim. A separate support/transport
  theorem can preserve halting semantics while validating only root support;
  `PROOF.md` spells out that extra theorem. Keep this secondary.
- The DFS job bound and Python runtime are not Lean reduction/RSS results.
  Use proof-friendly memoized finite maps; do not expand shared DAGs or
  normalize repeated whole maps through list-based `getD` accesses.
- Prove only fuelled-checker **soundness** initially. Fuel exhaustion must
  reject, and concrete kernel success establishes sufficient fuel for K215.
  Neither a full topological-sort completeness proof nor a formal universal
  `4*nn` fuel theorem is required. Checking the one derived scalar root-rank
  bound at the end can also avoid an initial generic cardinality proof.

## Files and next acceptance gate

- `PROOF.md`: exact hypotheses, recurrence proof, soundness/completeness
  argument, supplied-order distinction, and root-support alternative.
- `RankScopeContract.uncompiled.lean`: short no-hole abstract conversion
  from completion-rank/scope invariants to the **existing** `RMEquiv.WF`.
  This draft is uncompiled and is not the missing evaluator proof.
- `check_wellformedness.py`, `check_result.json`: owned finite evidence.
- `computed_summaries.json`: diagnostic output only; not a new certificate.
- `sources/`, `SOURCE_PINS.json`: pinned data/code inspected as text.

Adopt only after the generic evaluator soundness theorem is kernel checked,
the concrete K215 fold is kernel checked under the same memory budget as
the normalized lane, its old/new exact theorem and axiom closure agree, and
the affected full endpoint consumers are rebuilt. If one closed evaluation
still exceeds budget, use a proved compositional state transition interface
with bounded chunks; do not reintroduce independently supplied H/B/C arrays
or silently classify an uncompiled design as a reduction in verified work.
