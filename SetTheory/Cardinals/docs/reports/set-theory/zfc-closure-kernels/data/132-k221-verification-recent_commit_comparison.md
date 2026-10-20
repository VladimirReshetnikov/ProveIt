# Recent-commit intake for the sub-222 search

Reviewed through 98168e96ebd1ecbc297ed437a5e5a20f1e41256c (2026-10-20 04:20:53 UTC), checked again at 04:29 UTC.

## New baseline

Commit 71d760a1341ffd872c01e25641644c3593822edd adds ProveIt's conditional-K plus merged-G 222-state construction. Its source is distinct from our witness-request plus merged-G 222 construction:

- New: 4581 primitive leaves, 186 distinct internal source nodes, 13 tag-sharing aliases, 49 engine states = 222; maximum depth38; maximum zero run6.
- Previous: 4744 primitive leaves, 185 distinct internal nodes, 12 aliases, 49 engine states =222; maximum depth36; maximum zero run6.
- Thus the conditional presentation gains one extra alias but costs one source node. A sub-222 result could arise by preserving that alias while removing one internal node, or transferring that alias into the witness presentation.

The new source/table files are in repo222. Canonical table SHA256 60e21a040e58e2a2840b0f3d58ad3ee0e6ef4d0d5cdf1372d5a69355f1198ca1; inherited table SHA256 027b5e1cd5cae6cd158f9490021c13b0df395d8d7187739204d049b98236b06a; native table SHA256 c43b24bb8ffa6821ee2521e5bf610a36b08f6b7a59d837a14933a7afba9e60d4; source SHA256 6e6a863fd475a7508e9afab8e76b5291bf0541b4b2999b71c6ecea5fcd41c3ae.

Independent checks: replay/emitter.log verifies exactly And(Kc,RV) and G, and the two exact primitive-word replacements against conditional223. replay/build.log reconstructs the native table byte-for-byte using the conditional223 table, incremental compiler, and folds301→118,135→159. The inherited additional alias is18→180. replay/boot.log verifies the complete dispatch startup frame after409835 steps by both sparse and dense simulation. Universal literal-runtime replay is recorded separately in replay/runtime222.json when complete.

## Archive review

Commit98168e adds docs/incoming/K222_Construction_2026-10-20.zip, downloaded as incoming222.zip. SHA2564f677d8253846069a77dcac648a0a2bfe002ec8530886924ae3eba71e97e00d7: byte-identical to our completed witness+G222 delivery, not a third construction.

Commit5342a12 places Sources128–130. Source130 is the same mergedG223 machine/source as Source128 plus research. Its archive (commit6ab3e41) is research130.zip, SHA256e33435752381f6912701136e57eae8d57e32ff3b875d04369ddb10cd301a8c88. Extracted under research130/K223_Construction_And_Research_2026-10-20. New material includes symmetry+REL interpretation, negated-matrix K/polarity fusion, finite-only polarity229, and obstructions. No additional sub222 candidate is claimed.

## Claims boundary

The new conditional+G222 proof is an ordinary mathematical composition formalizable in ZFC, not a new compiled Rocq/Lean theorem and not a PA-internal proof. Universal runtime verification is separate from the logical calibration. Neither baseline is claimed minimal.
