# Validation record

Date: 2 October 2026.

## Mathematical scope

The article incorporates separately checked proofs of the weighted density estimate, the transition-uniform relative tail theorem for both probabilities, the exact switch at k=m+1, central and separated fixed-order matching, and the separated Lambert-branch inverse with qualified integer brackets. Approved source hashes are recorded in `source-hashes.json`.

The fresh integrated mathematical and attribution review passed with no required corrections, tied to TeX SHA-256 `9b81ead7ed2283ee215738a0929a56284c722b090e591e78b463960c415dc4cf`. Portable replay also passed: the ZIP was extracted with Python zipfile into a fresh directory, and `bash replay.sh --with-pdf` verified all manifest hashes, reran all three calculation scripts, matched all recorded JSON outputs, and rebuilt the PDF successfully. No executable permission bits were required.

## Fixed finite computations

`check_symbolic.py` independently derives the saddle displacement, variance correction, exponent and prefactor corrections, H3 identity, P1 identity, and c1 identity. It checks coefficient parity through order 10; the proof of all-order parity is in the article.

`check_inverse.py` checks the first two inverse cancellations symbolically, the derivative of L, the real Lambert branch identities, and finite high-precision crossings of an explicitly defined smooth log carrier. These are not exact-probability or integer-rounding checks.

`check_uniform.py` uses exact rational probabilities at 16 parameter pairs and mpmath quadrature at 65 decimal digits to evaluate the saddle formulas at R=0,1,3. The sample maxima of the normalized smaller-tail errors are 0.307223831873, 0.0819420489345, and 0.0346592177493. These are observed finite-sample values and are not uniform constants. Numerical quadrature is not interval certified.

## Rendering and packaging

The 12-page PDF compiled with no LaTeX warnings or overfull/underfull boxes. Every page was rendered at 100 dpi and individually inspected for legibility, missing characters, clipping, equation alignment, and page layout. After the final citation and sample-rounding edits, pages 1 and 11 were re-inspected; the other final page images were byte-identical to their inspected renders. PDF text extraction also passed. Build caches and page images are excluded from the archive.

The archive is built from an explicit file allowlist, with no third-party full text, symlinks, absolute paths, parent-directory traversal, hidden files, or executable-bit dependency. SHA256SUMS pins all included files except itself. The PDF is rebuilt into a separate output path during replay so the pinned delivered PDF is not overwritten.

## Limitations

No worldwide novelty certification, effective constants, stable numerical algorithm, interval-certified tails, endpoint-ratio uniformity, growing truncation order, optimal truncation, convergent series, or uncertified exact-rounding claim is made. A replay checks finite algebra and computations; it does not replace the analytic proof.

## Recorded toolchain

Python 3.12.14; SymPy 1.14.0; mpmath 1.3.0; pdfTeX 1.40.26 (TeX Live 2025/dev/Debian); Poppler pdftoppm 26.05.0.
