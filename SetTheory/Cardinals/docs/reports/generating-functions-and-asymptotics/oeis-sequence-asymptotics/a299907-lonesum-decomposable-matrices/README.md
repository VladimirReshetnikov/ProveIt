# Report 132

All orders asymptotics for square lonesum decomposable matrices (OEIS A299907)

## Read first

Report132.pdf is the reader article. Report132.tex is its complete editable source. The article proves a relative expansion through every fixed half-power order, gives C, c1, c2, an exact Gaussian coefficient recipe, and inverse ceiling brackets. Its constants in remainder estimates and onset thresholds are existential. Neither finite calculations nor this bundle certify an explicit finite-n error bound or worldwide novelty.

## Dependencies

Python 3.10 or later, SymPy and mpmath (tested with Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0). A pdfTeX/LaTeX installation with amsmath, amssymb, amsthm, geometry, lmodern, microtype, booktabs and hyperref is needed only to rebuild the PDF. No network access is needed once dependencies are available. The supplied PDF was built with pdfTeX 1.40.26 (TeX Live 2025/dev/Debian). PDF byte identity is checked within this environment; different TeX/font versions can produce different PDF bytes without changing the article.

## Routine verification

From the extracted Report132_bundle directory:

    python3 -B check.py
    python3 -B -O check.py

These check the closed inventory and every SHA-256 digest, exact fixtures for n=0..15, an independent composition/finite-difference count, exhaustive induced-P5-free counts through n=3, symbolic c1/c2, parity, inverse cancellation identities, and the coefficient-order-zero edge case. The guards remain active under -O. A changed manifest can legitimize a file edit for integrity purposes; the independent finite checks still reject the selected mathematical mutations used by qa.py. SHA-256 integrity is not cryptographic authorship authentication.

## Calculations

    python3 -B derive_general.py 0
    python3 -B derive_general.py 2
    python3 -B derive.py
    python3 -B validate.py --max-n 100

The first script is the arbitrary fixed-order symbolic recipe. Orders above two can take substantially longer. The separate direct expansion checks c1 using a different radical convention. Exact integer arithmetic supplies the counts, followed by 80-digit numerical evaluation for diagnostics. The archived diagnostics_3200.json records a longer run; repeating it is optional:

    python3 -B validate.py --max-n 3200

The stored diagnostic includes c3 as an additional consistency value; the article claims and routine symbolic checker explicitly display and test c1 and c2. Numerical residual convergence is evidence about implementation, not proof of the asymptotic theorem.

## Rebuild and full replay

Use new output filenames outside this directory so its closed inventory stays unchanged. Build, ZIP and QA receipt commands check the destination before doing work, reject existing files, bundle-local paths and symlink ancestors, and create output exclusively:

    OUT=$(mktemp -d)
    python3 -B build.py --output "$OUT/rebuilt.pdf"
    python3 -B qa.py --output "$OUT/qa_results.json"
    python3 -B package.py --output "$OUT/Report132_reproducible.zip"

The build script constructs a local TeX format and uses writable temporary TEXMFVAR/TEXMFCONFIG directories. It rejects failed compilation, overfull boxes, and unresolved references. qa.py checks normal and optimized runs, selected corrupted copies, unchanged inputs, two clean byte-identical PDF builds, and fresh archive extraction/rebuild/repacking. It does not perform visual inspection; the delivered PDF was separately rendered page by page and visually reviewed.

package.py --seal is a maintainer operation that deliberately replaces MANIFEST.json after intentional edits. It is not a verification command. The closed inventory rejects extra directories, special files and symlinks as well as unexpected ordinary files. The manifest lists every other bundle file; the verifier explicitly inventories MANIFEST.json too. The archive contains only the reader article, scripts, public-source citations, fixtures, and diagnostics. It contains no raw research notes or external source-paper PDFs.

## Scope

The exact EGF and enumeration are due to Kamano. Ordinary lonesum matrix asymptotics are prior work. The graph interpretation fixes both labelled shores. The source search is bounded and Khera's dissertation full text was not inspected. See sources.md and the article for details.
