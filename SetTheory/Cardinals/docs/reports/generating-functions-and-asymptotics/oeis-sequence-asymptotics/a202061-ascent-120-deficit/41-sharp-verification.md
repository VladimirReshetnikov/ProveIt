# Release verification

Verified 2 October 2026 UTC.

## Mathematical scope

The independent leading-order audit is in `audit/independent-audit.md`; final integrated transcription, auxiliary finite-height radius and exact inverse are covered by `audit/integrated-report-review.md`. The statement is an equivalent for the logarithmic deficit, not a multiplicative coefficient equivalent or an all-orders expansion.

## Source and PDF

- TeX SHA-256: `1e0019196acafab4899ef5dc405f8d8906267c36f6d40faf8991193d19b108f5`
- PDF SHA-256: `24ab7dfbd11e72e98216dc366ad7a73ef0e771352dd2f0a5c792abce1fa12251`
- PDF length: 10 Letter-size pages
- Two-pass LaTeX build completed with no overfull boxes, unresolved references or unresolved citations
- All 10 pages were rendered and visually inspected; no clipping, overlap, broken formula, missing glyph, or page-number problem was found
- After final corrections, affected pages 3, 4, 6, 9 and 10 were rechecked; the other page renders were byte-identical to the previously inspected images
- The final corrections explicitly round the cube root in the macro-count choice, use the actual increment consistently, restrict the radius-bracket parameter to (0,1), and identify positive Perron projections

## Reproducibility

`verify_all.sh` checks the exact release manifest file set and hashes when present, replays the author and independent sharp identities, validates the unchanged foundation manifest, and reruns both the foundation author and independent diagnostics. The producer replay passed; its output is in `producer-replay.txt`.

The copied foundation files preserve their original bytes and original internal SHA256SUMS. Build caches and page PNGs are excluded from the downloadable archive. The release uses a fixed LaTeX source date. A fresh-extraction replay of the frozen ZIP is recorded separately alongside the archive by the release coordinator.

## Boundaries

The finite computations supplement the proofs; they do not establish the asymptotics by fitting. The audit is research verification, not journal peer review or formal proof-assistant certification. Supplementary stronger local equivalents in the original kernel note are outside the main theorem's required and independently reviewed boundary. No second-order deficit, transseries, multiplicative amplitude or finite-data crossover claim is included.
