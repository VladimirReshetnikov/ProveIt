# Independent review of normalized K215 source certificate

**Verdict:** the 2,240-to-1,426 certificate compression is correct at the
ordinary finite-check level, and the generic Lean proof has the right semantic
interface. No gap was found in zero-padding or successor preservation. This
review did not compile Lean; the concrete kernel check has separate status.

The independent checker `review_normalized_certificate.py` imports none of
`normalize_certificate.py`, `graph_compress.py`, or upstream `gen_cert.py`.
It uses string pointers, a source-leaf interpreter, direct DAG traversal,
independent pointer arithmetic, segment evaluation and BFS graph construction.
Its receipt is `normalized_review.json`.

The checker is portable and does not write a receipt unless `--output` is
explicitly supplied. From the containing report packet:

```sh
python3 evidence/review_normalized_certificate.py
python3 evidence/review_normalized_certificate.py --repo /path/to/ProveIt
```

`--packet /path/to/source_normalization` overrides the default sibling
`source_normalization` directory. `--output /path/to/new-review.json` optionally
saves the printed result. Without `--repo`, the packaged source and DAG bytes
are checked against their pinned SHA-256/Git-blob identities. With `--repo`,
the source bytes are additionally compared with the supplied checkout. The
receipt states which scope was used. The recorded preparation run used both
checks; a standalone replay needs no repository or network.

## Confirmed numerical result

- The independently reconstructed literal-pointer graph has exactly **2,240** entries.
- The delivered normalized graph has exactly **1,426** distinct pairs: 1,425 decrement pairs and one halt pair.
- **814 entries are removed**, a 36.3392857% reduction.
- All **2,851 branch obligations** hold: one initial segment and two per decrement entry.
- The old-to-new map is surjective and preserves **both** successor indices.
- Quotient fibers: 707 singletons, 624 pairs, 95 triples. Their weighted sum is 2,240 and unweighted sum is 1,426.
- Every matched segment has exactly equal register-increment multiplicities, including register 5. Thus the omitted offsets are all zero; this is not inferred merely from matching register names at tests.
- The longest normalized path has 176 bits; 512-step pointer decoding comfortably covers every supplied encoded value.
- Decimal pointer values are positive sentinel encodings, stored as strings, and decode back to the intended paths.

## Zero-padding and successor argument

`ipeq P Q` identifies paths with the same infinite zero extension.
`tsite_ipeq` proves equality of the **entire observation**, including the bits
actually consumed. This follows from the already established `walk_ipeq` and
`pre_ipeq`, not from an unproved assertion about pointer arithmetic.

The key implementation detail is correct: successors are calculated from the
**consumed leaf path**, through `inc_path(pp)` and `brk(1,pp)`. They are not
calculated from the trimmed stored representative. Trimming raw pointers
before pointer arithmetic would be wrong: `[true]` and `[true,false]` have the
same zero extension, while incrementing these finite lists produces `[false]`
and `[true,true]`, which do not. The consumed paths for equivalent inputs are
equal, so the actual construction avoids that error.

The relation `Rel T` is saturated under `ipeq`. The generic checker proves
entry obligations at stored representatives and transports them to all related
pointers by exact `tsite` equality. Root segments and branch segments use equal
increment-count effects. Existing `Bisim.halts_iff` then gives the same
all-register root halting equivalence.

The generator also checks that no live nonzero suffix lies beyond a consumed
leaf at the relevant segment endpoints. It does not silently erase such bits.

## Provenance correction and final identities

During review, the downloaded source and DAG files had an extra trailing
newline. Parsed data was unchanged, so this did not invalidate the counts or
semantics, but it changed the claimed byte identities. The producing agent
corrected the files and regenerated certificate metadata. The final checked
source bytes equal the pinned repository's canonical source; SHA-256:

`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`

The final DAG file has 16,959 bytes and Git blob
`ad1775396daf0d351492a8d95c3af1d95bc33ea1`, independently matched against the
pinned repository tree. Its SHA-256 is:

`227d316cd61ce4781405c5abbd53e9f206bc70111c6c7f9237ecf7baf0a8517a`

## Boundaries for the main report

1. The 36.34% figure measures this certificate's entry count. It does not show
   36.34% shorter total proof source, kernel terms, compilation time, or memory.
2. A compiled generic checker theorem alone is not the concrete K215 result.
   The concrete `hs` and `ha` certificate checks must also be kernel-verified.
3. Python certificate generation, this independent finite audit, and Lean
   compilation are distinct evidence layers; describe their actual statuses.
4. The proposed source equivalence can reuse downstream theorems; it does not
   by itself supply a newly rebuilt exact-table ZFC endpoint.
