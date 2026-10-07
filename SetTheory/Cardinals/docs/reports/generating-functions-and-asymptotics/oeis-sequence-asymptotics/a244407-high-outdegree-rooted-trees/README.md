# Report 227

High maximum outdegree in rooted unlabeled trees

This package contains a detailed mathematical article about OEIS A244407/A244410, its editable TeX source, exact reproduction code and numerical diagnostics. The model is rooted, unlabeled, nonplane trees, and degree means outdegree. Maximum degree is exactly k.

The article proves an exact stabilized coefficient description, the first boundary subtraction, a sharp-base relative bound, an exact two-hub correction with separate all-fixed-order expansions, a first three-hub boundary coefficient, conditioned depth and decoration laws, and qualified Lambert-W inverse enclosures. The classical methods and constant are credited. The incomplete Goh–Schmutz full-text comparison precludes a worldwide novelty claim; see SOURCES.md.

## Contents

- report227.tex: complete editable article
- Report227.pdf: rendered article in a release archive
- code/: public exact tests and finite-order numerical engine, with its own README
- data/: labeled exact-generated fixtures and separately sourced OEIS entry samples
- SOURCES.md: attribution, source-access limitation and numerical qualifications
- build.py: source-preserving verification, PDF compilation and deterministic ZIP assembly
- MANIFEST.sha256: hashes of all source files, excluding itself and the two generated release files
- build_checks.json: release verification receipt, present in a built archive

## Build from an extracted archive

Use Python 3.10 or later. The exact suite needs only the standard library. The numerical suite requires mpmath 1.3.0, the version tested. A TeX Live installation with pdfTeX, LaTeX, Latin Modern, amsmath, amssymb, amsthm, mathtools, booktabs, microtype, geometry, hyperref, bookmark and enumitem is needed for the PDF. No network is used by the build.

Run from this directory, choosing a new output directory outside the extracted package:

    python -B build.py --out ../report227-build
    python -B -O build.py --out ../report227-build-optimized

The builder validates the exact source inventory and hashes, runs the supported-cap exact suite and order-five numerical diagnostics with explicit exceptions, compiles TeX in the output directory, rejects unresolved-reference or overfull-box warnings, verifies the source files were unchanged, and writes Report227.pdf, Report227.zip and build_checks.json. The optimized build propagates -O to its Python checks. Existing output directories and symlink output paths are rejected to avoid accidental overwrite. A release archive can itself be extracted and rebuilt by the same command.

PDF metadata and ZIP member dates are fixed. Byte-for-byte reproduction is expected for the same software versions and fonts; differing TeX distributions can legitimately produce a different PDF. Source and mathematical test reproduction do not require a bit-identical cross-platform PDF. The report date is 5 October 2026.

The code's finite supported limits are documented and enforced. Editing a source or fixture requires intentionally updating MANIFEST.sha256 before a build; otherwise the build fails, including for missing or extra files. The supplied manifest is an integrity check, not a cryptographic signature or a trust certificate.

## Mathematical qualifications

Every fixed-order asymptotic claim is a theorem about a fixed finite truncation. Numerical decimals are not interval-certified. The two exact sectors have independent remainder bounds; a finite algebraic truncation of the first sector can be larger than the entire second sector. A smooth inverse must not be rounded unconditionally near an integer threshold. Finite tests are diagnostics, not replacements for the article's proofs.
