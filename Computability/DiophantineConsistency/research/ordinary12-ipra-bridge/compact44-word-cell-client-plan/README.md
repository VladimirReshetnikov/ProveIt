# Draft compact-word to local-cell client

`CompactWordCellClient-DRAFT.lean` is **uncompiled**. It proposes a uniform
payload from the four `compactField` lookups used by `CompactWord`, attempts
to prove its Σ₁ definability and its agreement with `tileValue` at a bounded
row, defines word-indexed selector and payload-bit functions, and applies the
bounded-row aggregate to each `j < N`. The selector and bit definability
claims explicitly require a Σ₁-definable word. The proposed aggregate uses
only `CompactWord.tile_lt`; it does not yet exploit the marker or neighbor
matches, or connect the finite sums to a packed product or an actual graph
zero. No statement in this draft is a checked Lean result.

## Provider compatibility is an actual obligation

The checked [bounded-row exploration](../compact44-forward-cell-inputs-exploration/README.md)
used `/tmp/compact44-coefficient-decoder-explore/lib`. The checked
`CompactWord`/halt construction uses the marked-suffix author provider
`/tmp/ipra-marked-suffix-final-build-01/lib`. These are **not interchangeable**:
point-in-time SHA-256 comparisons show different objects for the following
same-named modules:

| Module | decoder-provider object | marked-suffix-provider object |
| --- | --- | --- |
| `Compact943Data` | `092cf01d0bf249e88f75c78a31eb69f15040dfe985f1e990b19b8d296b9bd9d4` | `9ed9ec865af1b8b3794328655ca7cb9161cb8573460c82f80c5db8c35db4bf7b` |
| `Compact943Decoder` | `5de069136857ac98530c177cbcba38435569202a8e8806ff9d01f5f45950e76b` | `371eec69acbaa97c3ff59b5f981726d529be5481851b8aa301a9b51421ed3044` |
| `CompactCoefficientDecoder` | `4e64948d97f2a22bb6fc3b45d80492b2410f6a0f8868d4b67feb020c65e39ff5` | `f796c257b8c98949750928b1847cd0a9749a6bcaf56941f88e7d780eaa238d8d` |
| `CompactTilePayload` | `5ac1da28dc3f648630e0b554e90df4643e2ddaeeb84c0542f73d85b5d92e49c2` | `2be7b3bb2fff2929d67a572811bb51576fb93da345763a104f09018a1f5d5409` |

Different object hashes do not by themselves prove that the source-level
statements differ; they do rule out silently treating the earlier object as
the already checked same-provider input. The marked-suffix provider also
contains `CompactMarkedTransport.olean` (SHA
`14e5aa75e98b7c5ce7e5d568325683f360ca1eb16901ae47f005f34856f4b2ec`)
and `CompactRowComplete.olean` (SHA
`c0b2764d505682b97b3558b28e01b13bec15b2c95f62b7576e4a6d0a7e54b1a5`).
These hashes are sampled, not a full source-closure or provenance audit.

## Next bounded build

1. Reserve the sole Lean slot. Use a fresh output root and a fresh source
   tree. Compile the exact recorded `CompactForwardCellInputs.lean` first
   against the marked-suffix provider and the existing guarded Foundation
   package library, producing a new object in the fresh output root; do not
   place or load the object produced against the separate decoder overlay.
   Resolve and snapshot the direct source imports `CompactCoefficientDecoder`,
   `ArithmeticStandardCasts` and `Mathlib.Algebra.BigOperators.Fin`, and
   retain the compiler's actual exit, diagnostics, axiom output and hashes.
2. Compile this draft against that freshly built object and the **same**
   marked-suffix provider. Check with `lean --deps` that the two direct project
   inputs resolve to the newly built `CompactForwardCellInputs` and the marked
   provider's `CompactMarkedTransport`; check module-name slots in the package
   provider as well. Freeze and compare source, direct object and companion
   hashes before and after each compile. The marked-suffix library is an
   overlay: for example, its coefficient decoder and standard-casts objects
   are symlinks into the Wang-chunk provider. Record each link's raw target,
   resolved path and target hash; alternatively compile against a separately
   frozen regular-file copy. Do not mutate the historical provider. Preserve
   any failed checks; do not report the
   proposed theorems as established until the client actually compiles without
   `sorryAx`.
3. The eventual halt-word client must use the actual same-provider
   `CompactHaltWord.halt_compact_word` result (or a documented coherent
   rebuild), retaining its model halt and dimension assumptions. Then prove
   the position and mask/no-carry claims needed to serialize these local
   functions into the graph's actual cell and `paramKernel` product.

`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib` was the package root of
the prior author runs. The marked-suffix provider and its associated audit
remain subject to the inherited transitive/package/dynamic and point-in-time
qualifications described in the existing receipts. This plan does not imply a
paired replay or resolve the retained-byte or iPRA endpoints.

`scan.py` records direct and target candidate slots, including symlink text,
resolved path and file hash, without launching Lean. Its initial conservative
version rejected the marked-suffix seed's direct symlinks; the retained
`observations/scan-attempt01.py` is that initial source (its location has
changed, so it is not itself a replay command). The corrected scan exited 0
and wrote `direct-scan.json`; running it with optimized Python exited 1 as
intended. The scan is a single point-in-time observation, not a guarded build
or proof of transitive, intermediate-link or dynamic-provider stability.
