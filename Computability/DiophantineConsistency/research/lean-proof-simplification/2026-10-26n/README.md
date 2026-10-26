# Further Lean proof simplification

This is the second source-specific review of ProveIt's DiophantineConsistency
Lean development, pinned to `b310142330df89e48413c8fce62e7de223e1c7d5`.
Read `report/proof_simplification_report.pdf` first. Editable TeX, complete
candidate examples, two unapplied patches, measurements, and validation tools
are included.

## What differs from the previous review

The review covers the 21-commit interval after
`60e9c5d620c6c387d932876cfa2d9376f64ea56c`. It compares the proposals against
five incoming ZIP packets and the sixth packet moved to the research archive.
The 75 scoped prior-idea families are exclusions, not renewed recommendations.
Only the nine families selected in the report are recommended here. The
novelty-decision records also retain screening questions, not all of which
became recommendations. This is relative novelty within the audited corpus,
not a claim of global originality.

## Contents

- `report/`: PDF, TeX, build script and visual QA record.
- `annotated/`: raw-parent decoder reuse and fused tree-decoder specification.
- `current/`: one-support, prefix-word, word-congruence and propagation candidates.
- `wang/`: optional color-indexed boundary view and reproducible line counts.
- `supplemental/`: explicit CRT congruence and binary graph-depth specialization.
- `incoming_audit/`: exclusion catalog, novelty comparisons and pinned archive evidence.
- `provenance/`: recent-commit review and source authentication.
- `sources/`: unchanged focused snapshot, 826 verified selected blobs.
- `validation/`: reusable source checks, 21-target future Lean replay plan and tools.

The separately verified MRDPCore source supporting the CRT proposal is under
`supplemental/evidence/`. The incoming ZIP archives themselves are not copied
into this package. To retrieve and recheck them, use the optional network
command `python3 incoming_audit/verify_archives.py --download`; add `--extract`
only if their source contents are also wanted. The archive hashes and immutable
references are supplied independently of that optional download.

## Verification boundary

Every new Lean candidate is **uncompiled**. No Lean/Lake runtime was available,
and none was installed. Byte checks, exact source comparisons, finite arithmetic
smoke tests and successful patch application are not Lean elaboration or kernel
proof checking. No performance improvement is established. The patches were
applied only to disposable verification copies, never to `sources/` or upstream.

The focused snapshot is not a full buildable Lake checkout. Actual validation
requires an existing full checkout at the pinned commit, Lean 4.32.0, the pinned
dependencies and built baseline imports. See `validation/README.md`; the replay
harness does not install dependencies. In particular, helper relocation in C3
and declaration reordering in C4 need an actual integration check beyond the
standalone probes.

The support tools inherited from the previous packet are identified in
`validation/README.md`; reusing them does not present their design as a new
proof-simplification idea.

## Offline checks

From the extracted folder, before generating extra files:

    python3 -B verify_bundle.py --strict
    python3 -B provenance/verify_snapshot.py
    python3 -B validation/source_validate.py
    python3 -B -m unittest discover -s validation -p 'test_*.py'
    python3 -B current/check_candidates.py
    python3 -B wang/measure_north.py

The byte manifest verifies this package's internal consistency, not its
publisher. Pinned Git blob hashes permit independent source comparison.
Strict inventory rejects extra build caches; omit `--strict` later if extra
outputs should be allowed. Modified listed files still fail the hash check.

The short archive root is `LeanReview2`. On Windows, use a short extraction
location if legacy path limits apply. The report build uses XeLaTeX; the future
Lean replay script targets Linux/WSL with Bash and GNU-compatible utilities.

Repository source retains its original license at `sources/LICENSE`.
