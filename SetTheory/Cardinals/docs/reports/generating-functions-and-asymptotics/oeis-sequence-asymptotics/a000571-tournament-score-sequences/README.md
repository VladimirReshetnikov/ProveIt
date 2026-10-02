# Tournament score sequences and weighted component asymptotics

This bundle accompanies the research report `report.pdf`. The editable source is
`report.tex`. It derives fixed-order corrections for all and strong tournament
score sequences and a uniform half-power expansion for a specified near-critical
component weight. It includes the logarithmically centered coexistence profile
and carefully specified inverse-location statements.

The exact generating function and leading count asymptotics are established
prior results. General renewal and heavy-traffic/heavy-tail mechanisms are also
prior art. This report supplies explicit local lattice refinements; it does not
claim an exhaustive novelty search or a conditional component-mixture theorem.

## Files

- `report.pdf`, `report.tex`: report and complete editable source
- `scripts/run_checks.py`: one command for the exact, symbolic, and numerical checks
- `scripts/check_exact_counting.py`: independent Landau enumeration through n = 10
- `scripts/check_scores.py`: exact integer recurrences through n = 1000 and constants
- `scripts/check_crossover.py`: normalized weighted recurrence and two-term models
- `scripts/check_higher_crossover.py`: corrected third term and fixed second corrections
- `scripts/uniform_generator.py`: finite half-power generator through M = 4
- `scripts/check_weight_inverse.py`: known-size component-weight inverse checks
- `scripts/verify_manifest.py`: packaged-file SHA-256 verification
- `results/*.json`: replayable numerical and symbolic outputs
- `requirements.txt`: pinned Python dependencies
- `build_pdf.sh`: PDF rebuild, keeping generated TeX formats and caches local
- `replay.sh`: complete checks and PDF rebuild
- `SHA256SUMS`: hashes of packaged files, excluding this manifest itself

No full third-party paper, external data download, or private review document is
included. Source citations and links are in the report bibliography.

## Requirements

The checks were run with Python 3.12.14, mpmath 1.3.0, and SymPy 1.14.0.
The PDF was built with pdfTeX 1.40.26 (TeX Live 2025), using standard LaTeX
packages, Latin Modern and AMS fonts. Bash is needed for the shell scripts.

Use an environment with the packages from `requirements.txt`; if needed, install
them yourself with `python3 -m pip install -r requirements.txt`. The replay does
not install packages or access the network.

## Replay

From the extracted directory:

    python3 scripts/verify_manifest.py
    bash replay.sh

The explicit `bash` invocation works even if an extractor does not preserve
executable bits. The verification program fails if an exact/symbolic assertion
or a numerical diagnostic envelope fails. It writes JSON and logs in `results/`.
The LaTeX build writes intermediates in `.build/` and replaces `report.pdf`.

To run only the checks:

    python3 scripts/run_checks.py

To rebuild only the report:

    bash build_pdf.sh

A normal TeX Live installation is sufficient. On minimal installations the build
script also locates the system TeX trees and generates a local `pdflatex` format.
Generated file dates are fixed for same-engine reproducibility; different TeX
versions may produce a visually equivalent PDF with a different hash.

## What the checks establish

The exact layer independently compares Landau enumeration, component counts,
integer component colors, the divisor recurrence, and the renewal recurrence.
The symbolic layer checks the displayed c1, c2, d4 and C2 identities.
The numerical layer checks 21 crossover points through M = 4 and 24 weight-inverse
cases. `results/verification.json` records their outcome and the source hashes.

The corrected analytic coefficient is

    d4 = (mu**2 / 2 - e2) / mu

The numerical generator handles integer-exponent kernels by finite polynomial
identities. Ordinary hypergeometric functions are used only at nondegenerate
half-integer parameters. The report gives a contour and reciprocal-gamma series
definition that remains valid when ordinary Kummer parameters degenerate.

The numerical outputs are non-interval diagnostics. Exact integer recurrences
are followed by floating-point evaluation of constants and weighted models;
weighted coefficient convolution uses double precision. More decimal working
precision does not turn these values into certified enclosures. The analytical
proof, not a fit to these finite data, establishes the stated uniform errors.

## Scope and limitations

- The logarithmic window has tau >= 0 and fixed upper constant C
- Every truncation order is fixed before n tends to infinity
- Error bounds on the 4**(-n) normalization are absolute unless explicitly relative
- No supercritical moving-pole theorem or growing-order expansion is claimed
- Two coefficient contributions are not asserted to be a conditional mixture law
- Inversion uses a specified one-variable model; weight calibration assumes known n
- Real inverse localization does not certify integer threshold rounding

The final section of the report lists further mathematical questions.
