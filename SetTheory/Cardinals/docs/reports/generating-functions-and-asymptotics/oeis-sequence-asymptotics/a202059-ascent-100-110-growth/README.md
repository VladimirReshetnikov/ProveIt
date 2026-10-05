# Report243

The Sharp Linear Logarithmic Constant for 100 Avoiding Ascent Sequences

5 October 2026. Standalone article and reproducible bounded computational companion.

## Results

For ordinary ascent sequences avoiding 100 (A202059), and for those avoiding both 000 and 100,

log u_n = n(log n - 2 log log n + log 2 - 1) + O(n(log log n)^2/log n).

Hence (log n)^2(u_n/n!)^(1/n) tends to 2. For 110 avoidance (A202060) and common 000/100/110 avoidance, the corresponding normalized-root liminf is at least 1/2 and limsup at most 2. Their constants and even their existence remain undetermined here.

The article proves finite upper and lower triangular comparisons, an elementary logarithmic estimate for the triangular sum, all-length transfer, explicit stars-and-bars rank decoding, three fiber bounds, and controlled two-term first-crossing inverses. The inverse remainders diverge in absolute size; no exact rounding or relative count equivalent follows. A dedicated final section lists open questions.

Report241's occurrence encoding and earlier conclusion are credited. Historical triangular enumeration and self-modified/matrix correspondences are prior. See SOURCES.md for exact scope and URLs. No third-party paper is included.

## Files

- Report243.pdf: rendered article
- article.tex and sections/*.tex: complete editable source
- code/*.py: bounded exact enumeration, encoding, construction, guard, and replay programs
- code/source_prefixes.json: finite source fixtures with URLs
- code/*_receipt.json and code/*.csv: deterministic reference outputs
- COMPUTATION.md: finite ranges, algorithms, and interpretation
- build.py: immutable source verification, checks, deterministic TeX compilation and archive creation
- MANIFEST.sha256: complete member-content integrity record, excluding the manifest itself

The manifest is not a digital signature. The archive contains only the public files listed by the builder's allowlist. No hidden review documents or third-party source PDFs are included.

## Requirements

Python 3.11 or newer, with no third-party Python packages. The PDF build needs pdfTeX/LaTeX, Latin Modern fonts, and the packages loaded in article.tex. The reference toolchain is recorded in build_checks.json by each build. On this toolchain every rebuilt PDF and archive must be byte-identical; other TeX/font versions may differ and will be reported.

All commands must run with -B and -X int_max_str_digits=640. The programs additionally enforce the cap in source, use explicit exceptions rather than removable assertions, and bound their inputs and work. Every spawned Python process has the same explicit safety flags. Large counts are hashed as unsigned big-endian bytes when necessary.

## Verify the source package

From the package directory:

    python3 -B -X int_max_str_digits=640 build.py --verify-only

This verifies all file hashes and the exact permitted file/directory inventory. It writes nothing into the source package.

## Reproduce the complete article package

Choose a nonexistent output directory outside the source tree whose parent already exists:

    python3 -B -X int_max_str_digits=640 build.py --output-dir /absolute/path/to/new-build

The builder recomputes all four JSON receipts under both normal and optimized Python, regenerates all five CSV views and the computational reproduction receipt, and checks each against its frozen reference. It compiles a disposable source copy with a private TeX format/cache and shell escape disabled. The output PDF must match the frozen PDF. It creates a deterministic stored ZIP, preserves fixed timestamps/modes, and verifies that the source inventory is unchanged.

The thirteen top-level outputs are Report243.pdf, Report243.zip, four mathematical/guard JSON receipts, five CSV files, reproduction_receipt.json, and build_checks.json. Build logs reside in logs/. Existing output paths, source-tree outputs, symlink ancestors, and dot or dot-dot path components are rejected.

## Replay the actual final archive

Run the trusted source package's script against the archive and its original build directory:

    python3 -B -X int_max_str_digits=640 code/reproduce_zip.py --archive /absolute/path/to/new-build/Report243.zip --original-build-dir /absolute/path/to/new-build --output-dir /absolute/path/to/new-replay

The command first requires the archive's member bytes to equal this trusted source tree, rather than executing arbitrary code supplied by an archive. It validates member names, file types, timestamps, permissions, sizes and other metadata. Two fresh extracted trees are built under normal and optimized Python. Every archive member and its metadata, both complete ZIPs, both PDFs, and every top-level output must match one another and the original build. All three source trees, the input archive, and original outputs must remain unchanged. The replay receipt is written outside the immutable source tree.

## Run only the finite checks

    python3 -B -X int_max_str_digits=640 code/verify_all.py --output-dir /absolute/path/to/new-checks

Individual programs also accept --output for a new external JSON file. Defaults run the documented bounded coverage. The --no-reference-comparison option on verify_all.py generates a candidate reference set externally for authoring; it never modifies frozen sources and is not the normal verification command.

These tests are implementation checks. They do not establish asymptotics by numerical agreement, global novelty, formal verification, or external peer review.
