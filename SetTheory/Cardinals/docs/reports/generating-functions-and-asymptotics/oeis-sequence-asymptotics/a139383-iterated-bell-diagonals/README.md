# Asymptotics of iterated Bell diagonals

The report treats A139383 and A261280 as one moving-depth hierarchical-partition family. It proves finite log-polynomial forward expansions and inverses of specified smooth models, and gives a separately replayable outward-interval proof that the leading amplitude lies between 2 and 4. The finer numerical estimate is exploratory, not certified.

## Historical attribution

Prellberg’s FPSAC 2002 slides, numbered slide 17 (PDF pages 55–59, final build on page 59), and Mishna’s 2005 summary of his 2002 seminar already state a pre-sum bivariate coefficient formula whose specialization gives the diagonal leading scale. They also use the parabolic-coordinate method. The report credits that overlap explicitly. OEIS conjecture labels do not establish novelty. No priority is claimed for the leading formula, method, or displayed coefficients.

Primary sources:
- https://webspace.maths.qmul.ac.uk/t.prellberg/talks/recurrence.pdf
- https://algo.inria.fr/seminars/summary/Prellberg2002a.pdf

This revision preserves the self-contained finite-contour proof, all-order remainder construction, interval certificate, and inverse results. See `CHANGE-NOTE.md` and `review/attribution-review.md` for the source-specific correction and review.

## Read

- `iterated-bell.pdf`: complete report
- `iterated-bell.tex` and `inverse-section.tex`: editable source
- `source/A139383.seq` and `source/A261280.seq`: official OEIS exports used for indexing/data checks

## Reproduce without network access

From an extracted directory, run:

    python verification/replay.py

The replay checks the manifest when present, exact sequence data and an independent EGF recurrence, exact rational correction and Abel-remainder generation through order 3, and the production 2048-panel interval amplitude certificate. Temporary outputs go to a fresh system temporary directory. Expected runtime is roughly a minute; symbolic and large-integer performance varies.

Dependencies: Python 3.12 or compatible, mpmath 1.3.0 (interval arithmetic), and SymPy (exact symbolic coefficients). Tested versions are recorded in `results/runtime.json`. No package installation or network access is performed by replay.

Individual commands:

    python verification/check_recurrence.py --max 260 --out /tmp/iterated-bell-counts.json
    python verification/generate_coefficients.py --order 3 --out /tmp/iterated-bell-coefficients.json
    python verification/verify_amplitude.py

The coefficient generator supports requested orders 1 through 8; large orders may be slow. Its degree assertions are finite checks, while the report supplies the arbitrary-fixed-order construction and remainder argument. The reported rational Abel remainder constants are rigorous analytic majorants, not fitted errors.

## Rebuild the PDF

    bash build.sh

Requires a TeX distribution with pdfLaTeX and the packages named in the source. The script also supports an installation with absent filename databases/formats by constructing local build files. It does not download packages. The mathematical replay does not require TeX or PDF rendering utilities.

## Verification limits

The interval calculation encloses complete angular panels with explicit analytic truncation and Fatou-tail bounds. It relies on correct outward interval operations in mpmath.iv; the arithmetic implementation is not itself proof-assistant verified. The analytic argument and certificate received independent mathematical/software review and replay. Neither finite coefficient tests nor numerical asymptotic ratios replace the proof.

A discrete threshold is not a canonical smooth inverse. The report gives a safe eventual integer bracket, which must be instantiated with effective validity bounds or neighboring exact counts for a specific target. No external OEIS or repository publication is included.

Optional exploratory digits can be recomputed with `python verification/explore_amplitude.py`, which additionally requires NumPy and SciPy. That calculation uses extended floating-point arithmetic and does not certify its digits; it is deliberately excluded from the mathematical replay. Official OEIS source-file attribution and CC-BY-SA-4.0 terms are retained in `source/NOTICE.md`.

## Detailed review records

- `review/mathematical-review.md`: the mathematical and software findings, including the forward, remainder, inverse, and integer-boundary checks
- `review/interval-certificate.md`: complete interval integration and analytic error justification
- `review/frozen-sources.json` and `review/FROZEN_SHA256SUMS`: exact reviewed source and artifact identities

These integrity records do not replace the proof or the runtime assumptions stated in the report.
