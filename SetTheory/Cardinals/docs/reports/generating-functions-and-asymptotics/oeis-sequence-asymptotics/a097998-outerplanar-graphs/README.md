# Report 170 Labeled outerplanar graph expansions

This release contains the PDF, editable LaTeX source, and reproducible exact-code companion for connected labeled outerplanar graphs (OEIS A097998) and all labeled outerplanar graphs (A098000).

The counted objects are abstract simple graphs on a fixed label set. The connected EGF has constant coefficient zero, even though the A097998 b-file prepends 1 at index zero. K2 is included as a block.

## Contents

- `Report170.pdf`: the mathematical report
- `Report170.tex`: standalone editable source
- `companion/`: exact and high-precision verification code, fixed input fixtures, generated results, and instructions
- `SOURCE_PROVENANCE.json`: sources, inspected versions, URLs, and saved-source hashes
- `build_pdf.py` and `release_tools.py`: deterministic, no-clobber PDF build
- `make_zip.py`: deterministic, no-clobber complete-release archive
- `SHA256SUMS`: SHA-256 hashes of every other release member

The report proves all fixed orders by a complex-uniform contour argument. The leading count equivalents, limiting shifted-Poisson component law, and general expansion machinery are established prior results. No worldwide-priority claim is made.

## Reproduce the mathematics

Use Python 3.11 or newer, SymPy and mpmath. See the companion README for exact commands and pinned tested versions. Tests require no network and use explicit exceptions rather than Python assertions.

The exact checks verify finite coefficient identities and stored fixtures. Numerical residual tables are diagnostics, not proofs of asymptotic convergence or certified decimal intervals. The asymptotic inverse has existential error constants and thresholds; it is not a certified finite-input inverse algorithm.

## Rebuild the PDF

On a Linux/POSIX system with TeX Live, including pdfTeX, LaTeX, Latin Modern, AMS packages, geometry, booktabs, array, microtype, longtable, and hyperref:

    python3 build_pdf.py --output-dir /absolute/path/to/a/new/pdf-build

The parent directory must already exist; the final output directory must not exist. The build rejects symlink path components and does not overwrite existing output. It compiles its own local format, disables shell escape, pins UTC metadata, stabilizes cross-references, and fails on settled TeX warnings or layout defects. Generated format/cache files stay in the new build directory. Byte identity is verified on the documented TeX version; different TeX/font versions may render differently.

The reproducible PDF is `Report170.pdf` inside that build directory. The PDF distributed in this release was rendered and visually checked on every page.

## Rebuild the archive

From an extracted release:

    python3 make_zip.py --output /absolute/path/to/a/new/Report170_Complete.zip

This reads only the release members enumerated by `SHA256SUMS`, validates their hashes, adds the manifest itself, uses sorted ZIP members and fixed timestamps, and creates the output exclusively. It refuses an existing destination. No source file is modified.

## Source normalization

The published BGKN amplitude decimal is inconsistent with its defining generating functions; it agrees to printed precision with 9/4 times the amplitude computed here. The origin is not established. Kang's thesis already contains the correct analytic normalization, although its decimal 0.008095 is inaccurate. The report distinguishes these versions and does not present the leading constant as a new discovery.

No source PDFs are redistributed. Source links and file hashes in the provenance record identify the inspected versions.
