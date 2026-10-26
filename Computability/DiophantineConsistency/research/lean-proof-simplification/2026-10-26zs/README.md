# Constructed-rank proof review — sixth iteration

This package proposes one local proof shortening in CurrentPackingRank2011:
`fourBlocks_cast`, complete file 138 to 127 physical lines. It preserves all
public statements, definitions, imports and hypotheses. The exact polynomial
certificate already exists in NativeSourceMask.packing_four_block; the proposed
client inlines it to avoid a duplicated expanded expression. This is an optional
brevity-versus-abstraction tradeoff, not new mathematics or infrastructure.

**All proposed Lean code is UNCOMPILED.** No Lean/Lake executable was available,
no installation occurred, and no upstream repository file was changed.

Source pin: 9d9d1123b39927d30363f1dcd53c23f0575c30ee.
The separate closing exclusion cutoff is recorded in baseline_audit.
All earlier research and incoming proposals are treated as applied. The initially
considered rank-growth cleanup is excluded under the earlier general power-growth
normalization proposal. Its artifacts and combined variant are comparison-only;
only arithmetic_candidates/fourblocks_certificate is selected for adoption tests.

## Contents and offline checks

- `report/`: editable TeX, PDF, preamble and rebuild script.
- `sources/`: focused immutable source snapshot, not a full Lake checkout.
- `dependencies/`, `comparison_sources/`, `provenance/`: separately bound evidence.
- `baseline_audit/`: assumed-applied ledger and exact source exclusions.
- `arithmetic_candidates/`: source-guarded builders, patches, full modules, metrics,
  selected candidate and clearly labelled excluded comparisons.
- `independent_review/`: independent mathematical/source audit, not kernel validation.

Run `python3 verify_bundle.py --strict` and
`python3 provenance/verify_snapshot.py` for byte/source consistency. The
arithmetic candidate checks require Python and SymPy; the latter was already
installed in the review environment. Run `python3 arithmetic_candidates/check_artifacts.py`
and `python3 -m unittest discover -s arithmetic_candidates -p 'test_*.py'`.
The source builder reproduces exact text rather than elaborating Lean.

Rebuild the PDF with `bash report/build.sh` (XeLaTeX and fonts required). Logs and
rendered page images are not part of the deliverable. Hash agreement and bounded
models do not prove the Lean scripts are accepted or the whole project builds.

In a separately authorized complete pinned checkout, test the selected replacement
module, its existing Checks module and reverse dependencies, then compare the changed
public endpoint axiom reports before adoption. Keep all regression checks.
Do not automatically apply the excluded comparison patch.

## Prior archive evidence boundary

The seven incoming source ZIPs were read and byte-verified during intake but are
not redistributed inside this focused package. The default provenance replay
checks their saved Git blob references against the pinned trees and explicitly
reports archive bytes as not replayed. Retained manuscript excerpts and selected
source documents have their own bindings. `--with-archives` is only for an
external copy supplied with those exact archives; its earlier full local receipt
is included, not presented as a sealed archive-byte replay.
