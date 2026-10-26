# DiophantineConsistency: fourth proof-simplification review

**All locally proposed Lean remains UNCOMPILED.** No Lean/Lake executable,
installation, upstream edit, axiom output, project build or performance result
is claimed by this package.

Read `report/proof_simplification_report.pdf` first. Editable TeX, exact patches,
full replacement modules, source evidence and offline replay tools are included.
The original source comparison is pinned to
`e652d21c413de59e4821f6e8e9b6a3a077bf5bfe`; later novelty screening is recorded
separately in `late_review/` and `late_novelty_review/`. It does not silently replace the source pin.

## Novelty versus source validation

The original review considered four families H1,H2,B1,B2. A newer packet arrived
before delivery. H1 and H2 are excluded from novelty: its periodicity proof and
exact canonical quotient certificate cover the same remaining obligations.
Their files under `helical/` are retained **only as superseded comparison evidence**,
not as proposals to adopt or line savings credited to this review. B1 is also excluded: packet w proposes a cyclic shared-edge architecture that
eliminates its remaining temporal-matching obligation. The final screen at 09d65a93c9df8684c1a226341d6a5120623d1cdb retains only B2: a
paired halted pass/finish allowedness proof. The full file changes 164 to 155 lines,
saving 9 including the private helper and wrappers. No second robust new mechanism
was found. Read `late_novelty_review/` before using the recommendation.

The historical `baseline_audit/` snapshot covers 21 placed packets a–u and prior
round3 proposals as already applied, with 25 semantic contracts and 168 overlapping
ledger rows. The rows are not 168 independent ideas. Historical novelty decisions
in that snapshot are overridden by the two late-review folders, not rewritten to imply an
audit took place earlier than it did. The all-applied baseline is a semantic
assumption, not a compiled composite patch checkout.

All four exploratory patches still have source-only checks. The supplied combined
future replay plan includes superseded H1/H2/B1 and is an evidence/comparison plan,
**not a recommended all-prior-applied integration plan**. Its 9 modules and 96 public
audit endpoints do not establish that the new proposals compile. Adopt only the
retained bridge patch after checking it in a complete current environment.

## Offline checks

From this directory:

    python3 verify_bundle.py --strict
    python3 provenance/verify_snapshot.py
    PYTHONDONTWRITEBYTECODE=1 python3 validation/source_validate.py
    PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s validation -p 'test_*.py'
    PYTHONDONTWRITEBYTECODE=1 python3 helical/validation/test_candidates.py
    PYTHONDONTWRITEBYTECODE=1 python3 bridges/validate_static.py
    bash -n validation/replay_candidates.sh

`verify_bundle.py` detects changed, missing and (with --strict) extra files;
it is not a proof checker or a publisher signature. Source Git blob identities
are separately supplied. The snapshot verifier checks 914 current selected files,
6 dependency excerpts and 11 comparison files, including all 637 active Lean modules.
This is a focused source snapshot, **not a complete Lake checkout**.

The optional baseline verifier requires a full checkout at the recorded original
pin. Historical packet bulk is deliberately not bundled; the selected source
bindings and original audit receipts are supplied instead.

To rebuild the PDF, use `bash report/build.sh` with XeLaTeX and the stated fonts.
Build products introduce files, so perform rebuilds in a disposable copy rather
than expecting strict original byte inventory to remain unchanged. PDF metadata
may vary; the sealed replay compares rendered pages and extracted text.

## Safety of the evidence

Python model tests and preserved theorem signatures are not Lean elaboration or
kernel checking. Supplied `#print axioms` commands were not run here. Compilation
receipts from other packets, where discussed, concern their exact source bytes,
not these different candidates. No externally sourced code was executed merely
to trust such receipts.
