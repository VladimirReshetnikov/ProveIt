# Attribution and provenance

Prepared for Vladimir Reshetnikov and the ProveIt project, 19 October 2026.

The original compact proof calculus, native set theory, register source and
254-state binary machine are attributed to **Mira-Cult**. The upstream Rocq
verification is attributed to **Jeff Ketchersid** and contributors, and the
compiler framework to **Andrew James Wade**. The ProveIt project and its
previous incoming research retain credit for all earlier source, routing,
initialization, transfer-loop and context-sharing reductions, including the
exact 240-state baseline used here.

The retained ProveIt input is pinned to commit
`13ec39ed43148b1807f51ed6e6528e1c84659562`. The original files under
`baseline/rotation240/`, including their own attribution, notices and
licenses, are preserved. Statements inside those historical notices concern
their original submissions and dates; they are not statements about the new
239-state construction.

The contribution of this submission is the complete combination of:

- A replayable 13-stage source transformation, including two rotations across
  an explicit break boundary, preserving the full ordered control graph.
- A repair of the changed decoder context followed by a new choice of shared
  decoder programs, yielding the literal 239-state table.
- A direct six-case, whole-tape fold certificate and ordinary simulation
  proof, plus an independently factored reconstruction and label/startup checks.
- Fresh complete unbounded runtime checks for the exact baseline, repaired
  reference, and final table; rejected-candidate diagnostics and bounded searches.
- The exact CP-interface model filters, alternative-formalism comparison,
  consistency-proof composition, manuscript and portable packaging.

The ordinary associativity idea and use of a predecessor tape bit to share
control states both occur in earlier work. The obvious direct push/copy
reassociation is already present as a rejected `obvious244` experiment in
the inherited runtime helper. The generic symbolic runtime proof method is
also inherited. No historical priority claim is made for these general
ideas, the standard finite/countable model methods, or the finite theories
and logical calculi discussed in the report.

`validation/independent_runtime.py` is byte-identical to the inherited helper
(SHA-256 `0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346`).
`validation/symbolic_runtime.py` adapts only its source pin, case count and
default paths from the earlier research engine. Its transition and induction
rules are unchanged. `validation/adapter_provenance.json` records the input
and output hashes and historical source location. These historical locations
are provenance records; the supported replay commands have no dependency on
those local paths.

New research text, scripts and certificates were generated with ChatGPT for
the user's requested incorporation into ProveIt. No additional licensing
restrictions are asserted over the newly prepared material. Inherited code
and source retain their original terms. The ProveIt and Wade licenses and
related original notices are included under `baseline/rotation240/licenses/`.

This package does not assert that an upstream proof-assistant development
was rebuilt during this work, or that it supplies a newly checked Lean/Rocq
endpoint for the final 239-state table. The exact evidence level is stated
in `README.md`, `report.pdf`, and `research_status.json`.
