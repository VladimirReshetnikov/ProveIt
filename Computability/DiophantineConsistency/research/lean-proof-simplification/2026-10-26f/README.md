# Simplifying the DiophantineConsistency Lean proofs

This package is a source-specific proposal study of VladimirReshetnikov/ProveIt at commit `60e9c5d620c6c387d932876cfa2d9376f64ea56c` (26 October 2026).

Read `report/proof_simplification_report.pdf` first. Its editable LaTeX sources and build instructions are beside it.

The archive has one short top-level folder, `LeanReview`. On Windows, extract
to a short location if your archive tool enforces the legacy path-length limit;
some unchanged historical source paths are deeply nested.

## What is included

- `sources/`: an unchanged, hash-verified snapshot of the inspected Lean sources, selected documentation, generators, and repository configuration.
- `inventory/`: reproducible source and import counts, distinguishing implementation-named files, check/audit files, and archival copies.
- `architecture/`: proposed shared interfaces and coordinate-packaging lemmas.
- `tactics/`: proposed local proof replacements and supporting pinned Mathlib API evidence.
- `circuits/`: circuit refactoring candidates, extracted exponent certificates, static comparisons, and reproduction scripts.
- `validation/`: source-audit and axiom-log tools, negative tests, and instructions for future Lean validation.
- `provenance/`: the pinned source manifest and offline source-verification scripts.

## Verification boundary

No Lean compiler or Lake executable was available in the review environment. Every new Lean file and replacement proof in this package is an **uncompiled proposal**, not a certified replacement. Python tests check source/data properties only. They are not substitutes for elaboration, kernel checking, or transitive theorem axiom audits.

The snapshot is deliberately focused, not a complete buildable ProveIt checkout. External repository namespaces and Mathlib dependencies are not bundled. Candidate replay requires a full checkout at the pinned commit, Lean v4.32.0, the pinned Mathlib dependency, and built baseline dependencies. The supplied scripts do not install software or modify that checkout automatically.

No upstream repository changes were made. Source-line savings are distinguished from byte savings, build-time savings, theorem-strength changes, and reductions in mathematical obligations. None of the latter is inferred merely from a shorter proof script.

## First checks

From the extracted package root:

    python3 verify_bundle.py --strict
    python3 provenance/verify_sources.py
    python3 verify_evidence.py
    python3 -B validation/test_tools.py

Run the strict byte-inventory check before generating build caches or other
outputs in the package. Later, omit `--strict` to check listed files while
allowing extra local build outputs. All these checks are offline and concern
bytes, source text, or Python tooling, not Lean proof validity.

The report describes a staged adoption order. Compile and audit one small candidate first; retain original public statements and compatibility checks before attempting wider generator or representation changes.

## Licensing

The included repository source snapshot retains its original license at `sources/LICENSE`. Source files and pinned upstream excerpts retain their original notices. This report and proposed examples do not replace the repository's formal correctness claims.
