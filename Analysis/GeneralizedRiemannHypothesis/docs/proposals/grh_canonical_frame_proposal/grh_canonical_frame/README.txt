A CANONICAL DUAL FRAME FOR THE GRH REAL-PLACE ESTIMATE
===================================================
Prepared November 27, 2026 (America/Los_Angeles).

Recommendation
--------------
Keep the canonical unnormalized negative dual frame in OneRealPlace.lean.
Retain its positive Gram matrix H and use a bordered Hua determinant integral.
This removes the specialized triangular orthonormal frame and its determinant
bookkeeping while recovering exactly the current public majorant bound.

The report contains complete mathematical proofs, a concrete Lean migration
plan, source boundaries, and comparison with all 28 existing proposal packages.
The standalone Lean support has compiled. The full substitution in the GRH
project has not been integrated or compiled; net line savings are unmeasured.

Start here
----------
canonical_frame.pdf          Typeset research report.
canonical_frame.tex          Complete editable LaTeX source.
formal/BorderedGram.lean     Six checked algebra/determinant theorems.
formal/lean_check.log        Actual compiler output and printed axiom sets.
formal/README.txt            Exact formal scope and reproduction instructions.
code/check_canonical_frame.py
                            Deterministic exact/numerical regression checks.
code/audit_one_real_place.py Source-region and lexical-use audit.
code/verify_sources.py       Read-only verification of pinned Git-object hashes.
artifacts/proposal_audit.txt Complete 28-package mechanism/exclusion matrix.
artifacts/one_real_place_audit.json
                            Source counts and external lexical occurrences.
artifacts/source_manifest.json
artifacts/proposal_text_manifest.json
                            Pinned source and proposal hashes.
artifacts/head_drift.json    Final current-head comparison, including tree hashes.
artifacts/checks.txt         Output of 717 deterministic regression checks.
artifacts/source_check.txt  Output of pinned-source hash verification.
SHA256SUMS                  Checksums for the contents of this archive.

Source snapshot
---------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Base commit: f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f
Lean: 4.35.0
Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679

The final head check at b47dc5361a5869231f930aa3f59a1c6b53a35f6b found the
entire proposal corpus and the four relevant real-place/Hua/helper source
files byte-identical to the base commit. The analysis remains pinned so
all source counts and references are reproducible.

Reproduce
---------
From this directory, using Python 3 with SymPy and mpmath installed:

    python3 code/check_canonical_frame.py
    python3 code/verify_sources.py /path/to/ProveIt

For the lexical audit, use a checkout at the base commit above:

    python3 code/audit_one_real_place.py /path/to/ProveIt --output /tmp/audit.json

The hash verifier reads Git objects and does not require changing HEAD.
The lexical audit reads working-tree files; its source-region coordinates
are specific to the pinned revision.

For the Lean support, from an available Mathlib checkout at the pinned
revision, with Lean 4.35.0 and matching compiled dependencies:

    lake env lean /absolute/path/to/grh_canonical_frame/formal/BorderedGram.lean

See formal/README.txt for the full verification scope. The optional standalone
lakefile and lean-toolchain pin the same versions for a fresh environment.

To typeset the report (TeX Live with latexmk, lmodern, microtype, xurl):

    latexmk -pdf -interaction=nonstopmode -halt-on-error canonical_frame.tex

To verify this archive's extracted file contents on a system with sha256sum:

    sha256sum -c SHA256SUMS

How to interpret the evidence
-----------------------------
The mathematical proof establishes the proposed replacement and exact constants.
The six Lean theorems establish core finite-dimensional algebra, not the entire
bordered integral or the GRH theorem. Their printed axioms are only propext,
Classical.choice, and Quot.sound. The 717 checks exercise identities and boundary
cases; they supplement the proof and are not a proof of RH or GRH.

437 physical lines / 330 code lines in OneRealPlace.lean are gross rewrite
targets, excluding the preserved public theorem statement. A 29-line / 26-code-
line helper may also become unnecessary. These are not measured net deletions.
No claim of a fresh full-project kernel replay or global mathematical priority
is made. The new contribution is the concrete application and refactor, relative
to the audited proposal corpus.
