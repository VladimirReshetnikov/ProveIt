# Delete the second source language from the K215 decoder proof

Pinned repository: VladimirReshetnikov/ProveIt at cbf94cb552a3b49509e0eee80e7455d4eb5974c6.

Status: read-only source review, exact finite data audit, and an uncompiled Lean checker pilot. No Lean or Rocq module was compiled. No repository source, machine table, source program, or remote branch was changed.

Production boundary: this simplifies the separately checked decoder-prefix component and its future integration. The maintained K215 simulation still uses `checkEdge`, all 105 site blocks, and all 6,176 counted guarded outcomes. This proposal alone does not shrink the current endpoint closure. In particular, a terminal action/table-row match is not a proof of increment, decrement, break, continue or halt semantics: residual primitive/return contracts remain mandatory.

## Result first

The decoder certificate's 202-node `sourceNodes` is not an independently useful intermediate representation. It is exactly the maintained 179-node `p215` program with its 23 distinct primitive leaves assigned extra node numbers. If the forks of `sourceNodes` are enumerated in their existing order, fork number j is precisely `p215Nodes j`.

All 179 local adjacency/primitive squares commute under this map. The decoder root 201 maps to program root 178. All 234 roles retarget, preserving physical states, suffixes, role indices and block references. All 281 checked physical blocks survive unchanged. Of 468 role branches, 371 are internal and 97 terminal.

Recommendation: index decoder roles directly by `RegisterPath.Program` nodes, and express terminal edges directly by the corresponding `RegisterPath.Edge`. This deletes a complete source-correspondence layer without assuming that a source node or physical machine state identifies a decoder role.

## Why this is new relative to the inspected proposals

The current computed-tree change replaces a large tree literal by `ptree p215`. It does not remove the separate `DecoderCertificate.Node` language, the 202-element `sourceNodes` array, `sourceTree sourceNodes 203 sourceRoot`, or `source_tree_eq`.

Earlier program-first proposals change the order of quantifiers: choose a role route and clock before introducing an arbitrary tape. Earlier coverage suggestions use decreasing source labels to avoid subtree-size arguments. Both are compatible with the present proposal, but neither removes the duplicate source representation.

The present audit establishes the exact representation deletion: a 179-label isomorphism on forks, a 23-label primitive projection, and all 468 retargeted role branches. It does not propose collapsing the 234 roles to 179 states.

## Current dependency boundary

1. `RegisterPath.walk` decodes the literal `Program`, with zero extension and an explicit consumed depth.
2. `DecoderSourceBinding.upstream_walk_reaches_routed` converts its result through `walk_root` to `twalk (ptree p215)`, then `LeafAt`.
3. `source_tree_eq` identifies that tree with a separate 203-fuel unfolding of the 202-node array.
4. `source_path_of_leaf` converts the leaf witness back into `SourcePath sourceNodes`.
5. `source_path_chain_routed` combines that second source-path relation with the role and block certificate.
6. `KDecoderPrefix215` reflects the arbitrary-tape execution into the zipper semantics.

The proposed route replaces steps 2–4 by induction on the existing successful `walk` equation. The arbitrary-tape blocks and zipper reflection are retained.

## New finite certificate interface

The uncompiled pilot `DirectProgramCertificateDraft.lean` supplies:

- A role containing `node : Nat`, now a node of the actual `Program`; physical `state`; short `suffix`; and two links.
- An internal link containing the same target-role index and block index as today.
- A terminal link containing the checked physical `Action`, but no separate primitive-node ID.
- `branch p r.node bit`, the source edge selected directly from the program.

For an internal link, the checker demands:

1. The selected source edge is `.node child`.
2. `child < r.node` and the target role's source node is exactly `child`.
3. The target suffix is the last two bits of `r.suffix ++ [bit]`.
4. The referenced block's entry/exit states agree with the two roles.
5. Its finite window is the appropriate nonempty suffix of the known local word; nonemptiness and positive duration remain discharged by `all_blocks_checked`.

For a terminal link, the checker demands that the source edge is not `.node _` and that the table's actual transition at `(r.state, bit)` is the stored action. The source operation and argument come directly from `branch p r.node bit`, not from an unconnected annotation.

The checker also validates `r.node < p.nnodes`, suffix length, and root binding. Its terminal case no longer needs a fictitious primitive-node rank. The decreasing-node condition remains on internal source references. This is the rank that corresponds to actual recursive decoding.

The pilot deliberately imports the old `K215Decoder` to reuse `formal` and the 281 blocks. It is not yet a smaller production dependency closure. To obtain the intended deletion, first split table/block declarations and their existing soundness facts into a source-independent module. Then the direct certificate should import that module instead.

## Minimal affected modules

The proposed prefix-library migration affects `DecoderCertificate.lean` (role/checker interface), `K215Decoder.lean` (split block data and retarget roles), `DecoderPaths.lean` (direct walk induction), `DecoderSourceBinding.lean` (replace or retire the array/tree bridge), and `KDecoderPrefix215.lean` (direct routed-entry and zipper clients). A separately named new module can carry the pilot while the old library remains intact.

The literal `RegisterPath.Program`, `RegisterPath.walk`, `KSource215Program.p215`, `KZipTape` and the arbitrary-tape block semantics remain unchanged. For this prefix-only step, no production simulation or site module needs to change: `KSim.lean`, `KFastSites215.lean`, `KSites215Batch000` through `008`, and `KSites215.lean` keep the current Boolean checks. Actual endpoint adoption additionally requires the separately proposed semantic-coverage interface and all residual primitive/return contracts; that is larger work than this source-representation deletion.

## Required semantic theorem, precisely scoped

Define a direct routed-entry predicate recording a role path, final role, final source edge, and final physical table row. It must retain the entire consumed prefix, not just the two-bit suffix or physical state.

A useful strengthened induction invariant is:

Given

- `walk p fuel n P i = some (e, d)`,
- a checked role `r` for the exact source node `n`,
- `Before t (a+i) r.suffix`,
- `t (a+j) = bit P j` for every `i <= j < d`,

there exist a block-chain clock, terminal state and terminal bit such that the chain starts at state `r.state`, head `a+i`, stops at head `a+d-1`, preserves the whole tape, and has the direct routed-entry witness for source edge `e`. The chain traverses exactly `d-i-1` internal links. Consequently its clock lies between `d-i-1` and `7*(d-i-1)` under the unchanged block-duration facts.

Proof outline:

1. Induct on `fuel`, generalizing node, consumed position and role.
2. Fuel zero contradicts the successful walk equation.
3. Inspect the exact program edge selected by `bit P i`.
4. For a primitive source edge, walk returns `d=i+1`. The checked role edge must be terminal. Return the empty internal chain at the current physical state, retaining the source operation and final read bit.
5. For `.node child`, the checked role edge must be internal. Use the existing `before_snoc`, `before_drop`, `before_window`, and arbitrary-tape block theorem. Recurse at consumed position `i+1` and the certified target role, then prepend the block.
6. Compose using the existing `chain_sound`, then apply the existing zipper reflection as before.

The interval bit hypothesis is obtained at the root from `Reads t a (consume P d)`. It is essential: reading `P` itself is incorrect when `walk` consumes implicit trailing zeros or truncates an unread suffix. Successful walk gives `i < d`. No elimination of a proposition-valued path into executable data is required: this theorem returns existential witnesses in `Prop`.

This is a new proof obligation, not a consequence of the finite Python audit. It should be implemented alongside the current theorem and checked on the exact same table before deleting the old correspondence layer. The independently proposed tape-uniform route/clock refactor may be composed later; it is not needed to justify this representation change.

## Coverage and compatibility

The new core consumes `walk`, the same operation already appearing in `KSim.Covered`. It does not itself establish that every input walk succeeds, primitive/return execution, or full K215 site coverage.

Keep all 6,176 guarded source outcomes. Existing production discharges its old checks; a replacement producer must preserve that coverage. Keep semantic-edge/Boolean-edge compatibility as a separate migration. The present maintained `KSim` still consumes fixed-fuel `checkEdge`; successful semantic reachability does not imply that the fixed-fuel checker accepts.

There are two API choices:

- Preferred internal migration: update the small decoder clients to the direct routed-entry predicate. Keep final machine/refutation/consistency endpoints unchanged. This changes internal exported decoder theorem types and therefore requires a caller audit.
- Compatibility facade: retain legacy theorem names/types in a separate module, deriving old nodes and witnesses from the direct program presentation. Do not claim total deletion while those legacy types remain in the maintained closure.

If the existing `leaf_prefix` API is still useful, a short generic `LeafAt -> twalk` lemma converts it to `walk` through `walk_root`. Such a wrapper does not need the 202-node source language. However, its *old exact result type* still mentions the old routed-entry predicate; preserving that type requires the legacy facade. Do not confuse preserving the mathematical endpoint with preserving every internal theorem type definitionally.

## Exact source and data evidence

`source_provenance.json` records 27 exact pinned Git blobs. The audit verifies both SHA-256 and Git blob SHA-1 before parsing. Inputs are read as inert text; no upstream generator, proof assistant, or received script is executed.

The finite audit records:

- 202 alternate nodes = 179 forks + 23 primitive nodes.
- 179 literal program nodes, root 178.
- 179 adjacency/primitive squares and all 468 role-branch bindings.
- 234 distinct `(program-node, suffix)` role keys; all physical states and role identities retained.
- 4,751 expanded leaves and 6,176 decrement-sensitive outcomes.
- Leaf depths between 3 and 47.
- Full-word decoding, appended unread suffixes, and erasure of a trailing zero run.
- Rejection of three perturbations: swapped fork labels, a changed primitive, and a changed root child.

The exact full mapping is in `NODE_AND_ROLE_MAP.json`. It is migration evidence, not proposed production certificate data. The direct roles contain their actual source labels; the mapping can be retired from production once the new theorem checks.

The 202-node literal occupies 3,132 UTF-8 bytes and 205 lines through the following blank line. `DecoderSourceBinding.lean` is 4,456 bytes and 100 lines. These are gross removal candidates, not a net saving: the direct checker, generic walk induction, updated clients and any compatibility facade must be counted. The main benefit is one fewer source language and one fewer correspondence proof, not a promised build-speed improvement.

## Acceptance tests and limits

1. Check the direct structural certificate against `K215Decoder.formal`, and separately retain the already checked arbitrary-tape blocks.
2. Compile the generic direct-walk theorem, direct root theorem and zipper clients. Print their axioms.
3. Keep a typed comparison client for the old and new primitive-entry statements on arbitrary tapes and consumed paths.
4. Rebuild all affected K215 endpoint consumers and verify final theorem statements and allowed axioms. Update maintained generators as well as generated sources.
5. Measure source bytes, proof-object size and clean build time separately. No current measurement establishes an improvement in the last two.

Rocq is not claimed to have the same duplicate decoder representation. The normalized source-certificate refactor recently adopted there is a different layer; this packet does not propose replaying it or replacing its known-good checker.

## Reproduce the owned finite audit

Run `python -I -B audit_direct_program.py --output-dir /tmp/k215-direct-program-audit` from this directory or give its absolute path. This verifies source identities, parses the two literal graphs, and writes audit/mapping JSON in the chosen output directory.

Run `python -I -B make_direct_role_sketch.py` to regenerate the uncompiled direct-role pilot. This script executes only the owned parser via `runpy`; upstream sources are never imported. No compiler is invoked.

Attribution: source programs, machine tables, existing decoder roles, arbitrary-tape blocks and proofs are inherited ProveIt work. The new contribution is the exact direct-program source audit, representation-deletion proposal and uncompiled checker pilot. Source comments and existing attribution remain intact.
