# Simplifying the K215 correctness proofs

Research package for ProveIt at commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

Read `proof-simplification.pdf` or its editable source
`proof-simplification.tex` for the proposal and evidence boundaries.

## Status

The Lean and Rocq proposals are uncompiled research candidates. Included static
and finite checks do not establish formal proof correctness or a full endpoint
build. No received repository program or build script was executed during the
research. No machine-state reduction is claimed.

## Verify the sealed archive

Extract into a fresh directory, then run `python3 verify.py` before editing or
rebuilding anything. Python 3.10 or later with only the standard library is required.

The verifier checks the fixed SHA-256 manifest, runs only the specifically
listed newly authored checks in a temporary copy, and checks that the original
package (including the manifest) has not changed. It refuses `python -O` and
`python -OO`. It is not a security sandbox and a manifest is an integrity record,
not a cryptographic signature or independent provenance attestation.

## Rebuild the document

Use a separate working copy. A standard TeX Live or MiKTeX installation with
Latin Modern, AMS mathematics, geometry, microtype, booktabs, enumitem, listings,
hyperref, and fancyhdr can run `make pdf`. Shell escape is disabled. Rebuilding
changes derived files, so it intentionally invalidates the sealed manifest.

## Artifact inventory

- `review/`: exact current source snapshots, source/commit ledgers, novelty review.
  There are 174 endpoint snapshots and 29 additional compatibility snapshots,
  with one 203-source ledger. No second full baseline tree is duplicated.
- `lean/`: 12-file uncompiled generic-spine patch, candidate files, inert originals,
  exact-move/import audit, and newly authored reproducible builder.
- `audit/`: separately written source/patch and finite replay checks, compact
  reviews, support data and recorded results.
- `rocq/`: newly authored finite replay and boundary tests; pinned inert source
  and data; uncompiled Lean module and Lean/Rocq integration fragments.

The root verifier executes only the six named new Python checker entry points.
The reproducible candidate builder is included but is not needed by that verifier.
Copied source `.lean`, `.v`, and `.py.txt` files are inert inputs, never executable
steps in the verification harness. Preserve their original attribution notices.
