# Historical sphere audit with authenticated original sources

The current checkout has two expected source-hash mismatches, not one. This
packet preserves the original auditor, proof text, graph files and certificate.
Its read-only adapter supplies the two exact historical Git blobs to the
unchanged auditor in memory; all other input reads follow the historical
`pinned` function unchanged. The auditor recomputed its graph, degree, port,
mutation and other checks and matched its historical certificate byte for byte.
This is a replay of the *historical* finite audit, not a revalidation of the
current Lean source or provider graph.

## Source provenance and scope of changes

The original auditor and both original blobs are authenticated against commit
`a9bba4836516478cc5a052b9986662de628ac320`. The compared newer blobs are
authenticated against `79ddf75e93efa7b8c83600e64651479cfd7dc4e7` and against
the current tracked source bytes. This checkout need not remain at that HEAD;
if either relevant current file changes, the adapter fails closed.

| Source | Original SHA-256 | Compared current SHA-256 |
| --- | --- | --- |
| CarrierScaledAuxiliary118.lean | `2e222efd3b40626e6734fe30e5b7239fb7a7abd5fd9c14bee8e4a238c237c620` | `174c685cf1669080cccb3760a10317aff0c99bc439bf8070eeed525ec37bff04` |
| CarrierNonzeroSpheres.lean | `f2fb2bfc613e152e9b62d690d1564b41735f34dd2f7ec71c1a5980212b4ed51a` | `481f68dd519db210d2b81dd2756002e2bfecbf4744f03f143051c8f029ecebe9` |

For the scaled carrier, commit `ca3ebb30333ab7078fc3a7893ba36fef7a14efe2`
replaces the local proof of positive integer beta by the shared theorem
`CurrentMasks2011.beta_pos_int`. The adapter confirms this exact replacement
accounts for the entire source-byte change. That commit also introduces the
shared lemma and records paired source-ordered builds, with provider and
umbrella limitations in its commit message. This packet does not replay or
independently authenticate those builds.

For the sphere carrier, commit `6f53b13909` refactors the proofs of the two
current positive-zero endpoint equivalences into an existential congruence;
`ca3ebb3033` subsequently replaces the local beta-positivity proofs with the
shared lemma. The adapter checks that the bytes outside those two proof blocks
and the two theorem statements themselves are unchanged. It also pins the full
Git diff. This is a source comparison, not a proof that the rewritten Lean
bodies elaborate against the currently resolved providers.

The other four direct Lean pins used by the auditor still match: `Carrier65`,
`NearSquareNormZero`, `NearSquareNormZeroChecks`, and
`CarrierNonzeroSpheresChecks`. The unchanged audit additionally checks its
other pinned inputs and exact graph/certificate bytes. These checks do not
authenticate every transitive Lean import or compiled object. Its graph files
still name the historical sphere source hash; the historical proof text and
certificate still name historical source hashes.

## Why not just update a pin

Changing only `SCALED_LEAN_SHA` encounters the stale sphere-source pin next.
Changing both also changes the audit's expected graph metadata, graph hashes,
and certificate content, which in turn affects consumers that pin those
artifacts. The historical `PROOF.md` itself records the old scaled source.
Retain these records as historical evidence. A separate current-source audit
would need explicit new source and proof-text pins, newly generated graph and
certificate artifacts, updated consumer bindings and independent review;
source comparison alone does not establish current provider or axiom closure.
The independent fresh-base `bind_graphs.py` answers a narrower expression/DAG
comparison and does not substitute for this historical degree/port audit or a
current Lean replay.

## Reproduce

From `Computability/DiophantineConsistency`, with the specified Git objects
present:

    set -o pipefail
    timeout 55s python3 -I -S -B research/fourteen-nonzero-spheres-historical-source-replay/check.py | cmp - research/fourteen-nonzero-spheres-historical-source-replay/receipt.json

The adapter checks the historical auditor's complete bytes, both Git blob
pairs, the exact scoped diff and current source bytes. It intercepts only the
two named source reads; all other reads and the bytewise historical receipt
comparison are performed by the original auditor. It executes that standard
library audit in-process, with memory and CPU limits, and writes no historical
artifact. No Lean, build, staging or provider validation was performed.
