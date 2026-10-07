# Report190: hexagonal spiral Fibonacci asymptotics

This is the authored offline companion to Report190. It contains a complete
manuscript, exact integer/rational verification code, bounded attributed OEIS
fixtures, and deterministic release tooling. It requires no network access.

The two sequences use the same hexagonal adjacency rule with initial data
(a0,a1)=(0,1) and (1,1). They correspond respectively to A094926(n) and
A094925(n+1). Thus C1/phi, rather than C1, is the amplitude in the original
A094925 indexing. Here phi=(1+sqrt(5))/2.

The report proves convergence to positive amplitudes, supplies exact rational
amplitude enclosures, constructs the universal fixed-order stretched-exponential
corrections with the full side/corner layers, describes their leading profiles
and sharp square-root-phase envelopes, and states an error-aware integer inverse.
The all-order result means every fixed truncation order, not convergence as the
order tends to infinity. Leading sector profiles cannot replace exact operator
coefficients at the next exponential scale. A logarithmic ceiling alone does
not always recover the integer inverse.

## Quick verification

Python 3.10 or newer is sufficient; no third-party packages are required:

    python3 -I -S -B reproduce.py
    python3 -I -S -B test_build.py
    python3 -I -S -B -O test_build.py

The replay runs exact checks in ordinary and optimized Python and requires
byte-identical canonical results. It does not modify this directory. Detailed
commands and build safeguards are in README_REPRODUCIBILITY.md.

The mandatory verifier checks:

- All 79 supplied integer terms: 41 from A094926 and 38 from A094925
- All 106 supplied A258639 digits and all 77 supplied A094925 amplitude digits
- 1,162 coordinate/table rows through stage 19, extended to all 30,403 rows
  through stage 100 for each of the two seeds
- 19 exact full-stage forcing identities in Q(phi)
- Exact first-correction tail identities at 1,159 rows and 82 direct operator
  and stable-convolution sample comparisons
- Independent certificate arithmetic in the basis 1,sqrt(5)
- At least 120 truncated fractional digits for C0, C1, and C1/phi
- 83 explicit type, domain, structural, and fixture-corruption rejections

The receipt includes each exact rational endpoint as a hexadecimal numerator
and denominator, reproducible formulas and square-root enclosure precision,
the certified 120-place truncations, and outward 110-place decimal pairs.
Each printed pair has only 109 shared fractional digits. The stronger
120-place checks use the underlying exact rational bounds, not those displays.

All mathematical validation uses explicit exceptions, never removable asserts.
Finite checks supplement the manuscript's proofs; they are not proof by sampling.

## Building the release

With an installed pdfLaTeX distribution and its packages/fonts:

    python3 -I -S -B build.py --output "$(dirname "$PWD")/report190-release"

Use a fresh sibling output directory with an existing parent. The output is
Report190.pdf, Report190.tex, Report190_code.zip, and ARTIFACTS.json. The ZIP
contains the same PDF/TeX, authored code/docs, bounded fixtures, generated exact
receipts, and a checked closed-inventory SHA-256 manifest. Existing output is
never replaced. Optional floating diagnostics are never run by the build.

See DATA_SOURCES.md for source attribution and bounded research scope. No
unpublished research file, raw OEIS record, downloaded program, or prior report
is redistributed. The public build infrastructure was adapted from the
preceding authored report; the mathematical modules here are specific to this
hexagonal model.
