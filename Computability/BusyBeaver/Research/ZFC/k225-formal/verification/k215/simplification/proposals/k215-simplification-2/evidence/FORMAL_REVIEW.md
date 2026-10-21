# Independent review of the new CM215 Lean transfer

Review date: 2026-10-21. Scope: `PositiveSimulation.lean`, `MarkerTransfer.lean`, and `CM215Exact.lean` in `/dev/shm/zfc_simpler_work`. This is a mathematical/source review; the reviewer did not launch a second compiler.

## Result

No mathematical correctness defect was found in the reviewed transfer theorem.

- `PositiveSimulation.synchronized` obtains a target time k at least n after n source steps because every local block has length j+1. No uniform block bound is needed.
- The reverse implication in `halts_iff` is valid: if the target has halted at time n, its stable halting predicate holds at time k≥n. Synchronization at source time n and halting agreement then imply source halting. This handles halting inside a target block and supplies genuine reflection, not only forward simulation.
- `Tape = Int → Bool` represents the whole bi-infinite tape. `write_read` proves function equality; the one-/three-step blocks preserve the whole tape and exact integer head position. No finite support, zero exterior, or register-frame assumption occurs.
- The old-machine invariant has three clauses. The auxiliary clause at control156 is sufficient: every incoming edge there writes1 and moves left, placing a1 immediately to the right. The exceptional156/1 transition then reaches old176 on current1, so the zero-branch predecessor-marker obligation is vacuous. No unjustified assertion about arbitrary starts inside modified controls is made.
- Initial control0 satisfies the invariant for every tape and integer head. The relation identifies the target configuration with the entire lifted source configuration, rather than only a tape prefix.
- Halting states are totalized as self-loops solely in the evaluator; `Halt` remains the absence of an outgoing row. This gives the target halting stability used in the generic theorem.

## Literal-table review

An independent Python parser extracted both literal `match q.val` tables from the Lean file. Every one of their430 rows agreed with the corresponding pinned native table:

- old: `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`;
- new: `e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252`.

Each has exactly215 working labels with both symbol rows. Initial label0 is working. Every outgoing successor is working or the distinguished halt254;254 has no row. Hence the other labels of the ambient `Fin303` type cannot be reached from the designated start. The finite count, totality, closure, and halt facts are also theorem statements in the Lean file. An explicit induction packaging “reachable nonworking label iff254” would be convenient for integration, but the supplied finite premises already establish it mathematically.

## Scope boundary to preserve

The new modules establish a formal equivalence between two exact native tables in their standalone TM semantics. They do not themselves instantiate the existing `KEndpoint215` ZFC theorem. A semantics adapter and the known native-to-dense renaming must connect `CM215Exact.old` to the repository's `machine215` endpoint before describing the contribution as a newly compiled end-to-end ZFC endpoint for CM215. The source comments currently describe this boundary correctly.
