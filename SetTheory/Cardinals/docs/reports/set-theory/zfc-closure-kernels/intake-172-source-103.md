# Source 103: source boundary, a different 239-state machine

Package `ZFC_239_State_Construction_2026-10-19.zip` (arrival `83fd358548`, placement
`07194e5b4d`, prefix `103-bound239-`). Pinned to ProveIt
`13ec39ed43148b1807f51ed6e6528e1c84659562`. The main report, its PDF,
`source_encoding/source_search.pdf` and the delivery README are archive-only. Members
are mapped in [the placement map](data/intake172-placement.json).

## The machine

[`data/103-bound239-candidate239-zfc_boundary239.tm`](data/103-bound239-candidate239-zfc_boundary239.tm)
is the canonical table: 239 working states, start 0, dispatcher 84, halt 239, SHA-256
`666f5bf1…`. The inherited-label table, SHA-256 `d061770f…`, has start 95,
dispatcher 96 and halt 254, and **no start directive**. It saves a state in a
different place from Sources 101/102, in three steps.

1. **Source reparenthesization.** Thirteen stages with 25 rotations take the register
   source DAG from 225 to 224 nodes (internal nodes 202 → 201). No instruction
   occurrence, register operand or control-flow successor changes; all 6,455 leaves
   and 23 leaf kinds are preserved. The maximum path length falls from 51 to 48, and
   the maximum zero run stays 6. The last two rotations cross a trailing explicit
   break, a case that a conservative "all three chunks closed" rule had excluded.
   The certificate is [`…formalism-extra-rotation_certificate_results.json`](data/103-bound239-formalism-extra-rotation_certificate_results.json);
   the new source has SHA-256 `7fd152d1…`.
2. **Decoder repair.** The new source disrupts a decoder context. A charged repair gives
   the 240-state intermediate `boundary240` (SHA-256 `19cd7f78…`): 37 rows of 20 decoder
   states change. With the split below, boundary239 differs from the 240 table in 40
   retained rows of 23 states, between 61 and 237, and deletes 218.
3. **Context split.** Old state 218 is split by the bit immediately behind the head. Its
   former helper 223 is reused for one role and its other role merges with 179, so three
   control roles occupy two states. Six exact two-cell block identities prove halting
   equivalence for **every binary initial tape** at the common start state, by a globally
   inductive incoming-tag relation and with no runtime guard
   ([`…candidate239-fold_certificate.json`](data/103-bound239-candidate239-fold_certificate.json)).

The package's stated new idea is that this **changes the choice of shared decoder
programs**, not merely identifying two existing transition rows.

A second, independent constructor reaches the identical final table by a four-case
merge from a different 240-state factoring (`candidate239/reference240_old.tm`, SHA-256
`fbe421d2…`).

## Evidence

- **Unbounded runtime** on the new source: 8,386 cases. The rule counts are 2,322,575
  for the original 240, 2,252,241 for boundary240 and 2,247,513 for the final 239.
  The minimum duration is 13 throughout.
- **Exact blank startup**: 409,691 steps to the same full frame as the 240-state
  candidate (gap 117, 351 one-cells, 167 value-one spares).
- **Source and seed identification**: the 6,455 source triples and the logical seed
  are extracted from the pinned Lean definitions
  ([`source_interface`](103-bound239-source_interface-README.md)), with an audited
  register-path semantics for every instruction
  ([`semantic_interface`](103-bound239-semantic_interface-README.md)).
- **Endpoint audit**: [`…formalism-endpoint239_audit.json`](data/103-bound239-formalism-endpoint239_audit.json),
  `PASS_ORDINARY_ZFC_ENDPOINT_AUDIT`.
- **Rejected intermediates**, kept because they show why both the source change and
  the decoder change are necessary: `reassoc239_old.tm` has 702 failed minimum-register
  cases and `boundary239_provisional2_old.tm` has 690. A counterexample to their runtime
  contract need not be reachable from blank input.
- **Rejected scanner shortening**, with 99 finite counterexamples (`scanner/`). A sound
  baseline zero/nonzero invariant and heuristic signatures (`semantic/`). Bounded C++
  fold searches with a positive control (`state_folds/`); the successful context split
  lies outside the pair/block/deletion classes they test.
- An alternative-formalism and model-filter analysis (`formalism/`) and a finite flat
  container diagnostic.

## Non-claims (kept from the package)

- No new Lean or Rocq kernel theorem and no serialized PA derivation for the 239 table.
- The upstream calibration was not rebuilt.
- The negative search results establish no lower bound on the state count.
- No minimality or exhaustive novelty claim.
- The source-only DAG file keeps some historical node IDs; its array length is neither
  the reachable 224-node count nor the machine's state count.

## Relation to Sources 101/102

This construction and the delayed erasure touch disjoint rows, and they compose. See
[the combination](intake-172.md#the-combination-238-states).
