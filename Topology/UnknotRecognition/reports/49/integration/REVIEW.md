# Proposed integration into ProveIt

Suggested review-only destination:
`Topology/UnknotRecognition/fast/source_anchored_research/`.
The article may be stored in `synthesis/` after reviewing its theorem hypotheses.
No existing file was mutated and no automatic patch is supplied.

## Theory changes

Supplement `primitive_projection.tex` and `primitive_forest.tex` with the
saturated-kernel/cofactor theorem and reachable/allocated gate distinction.
The existing exponential recurrences remain valid coarse upper bounds but
are not needed for frozen-source raw epochs. Short raw phase depth is not
required for polynomial encoded cost; exposure and resets still need bounds.

## Minimal runtime seam

1. At a verified raw boundary, snapshot only root-reachable nodes, all original
   relator slots, and live labels. Retain the complete source PD/presentation
   prefix in the existing certificate host.
2. Keep the source circuit immutable while composing a monomial table. Recompute
   source summaries when the table changes: source node identity alone is not
   a valid cache key for current-support eligibility.
3. Validate every batch against the pre-batch state. Preserve all unselected
   slots. A table by itself is not a nonabelian certificate.
4. Run independent replay before authorizing any conclusion; proper powers need
   the host's source-established torsion-freeness invariant.
5. Export only at a genuine boundary that requires a conventional word circuit.
   After a verified nonmonomial operation or normalization, freeze a NEW source
   and account for its encoded size and cost.

`src/anchored_unknot/native_adapter.py` implements only steps 1 and 5 as a
protocol adapter. The v1 research certificate is not accepted by, nor a silent
replacement for, existing native versions 6 or 7. Direct anchored forests
remain an extension to implement.

## Source comparison

Inspected implementation commit:
`7518823550fbc8c217bc8be0113fe52002e77465`.

Run with a matching local checkout:

```sh
python -B integration/check_native_source.py --checkout /path/to/ProveIt
```

It verifies the Git blob SHA-1 of the full `primitive_projection.py` file and
then compares the copied `apply_projection` function's AST. A different head
requires review rather than bypassing the failed check. This command was not
executed against a complete checkout for the delivered bundle.

## Required acceptance evidence

Keep all existing defaults until complete-call measurements support a change.
Run the whole native unit suite and actual-diagram source-reconstructing replay.
Test both native literal and compressed checkers, proper-power prefixes, all
legacy proof versions, normalizer handoffs, cancellations, allocation limits,
label renaming, repeated/empty relator slots, and unselected raw zero words.

Run randomized paired whole-call measurements with A/A controls. Include source
reconstruction, donor discovery, proof creation, independent replay, exports,
and all relevant pipeline stages in the intended timing contract. Keep
whole-call and isolated-kernel measurements separate. Retain failed runs,
nondecisions, overhead, raw samples, and code hashes. The delivered maintenance
benchmark deliberately does not meet this whole-call timing contract.

Memory accounting must include the host arena, immutable snapshot, source-based
summaries, image table, proofs, temporary scans, and any conventional export at
once. Cooperative work counters and node caps do not bound every Python object.
