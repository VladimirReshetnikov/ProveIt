# Delayed digit stabilization

A research note dated 19 September 2026, prepared for Vladimir Reshetnikov.

## Main result

A public question asks whether, for every integer a >= 2 not divisible by 10,

    S_a(b) = v_10(a^(10^(b+1)) - a^(10^b))
    D_a(b) = S_a(b) - S_a(b-1)

always satisfies D_a(b) = 1 for b >= 3.

The answer is no. The smallest counterexample is

    a = 3*2^99 + 1 = 1901475900342344102245054808065.
    S_a(2) = 100, S_a(3) = 102, D_a(3) = 2.

The article proves minimality, gives an exact onset formula and the smallest
counterexample at every stage, computes the natural density of exceptions,
and develops arbitrary-radix and fast-growing-index extensions.

The selected sequence a^(10^b) is not genuine tetration a^^b. The article
explains that distinction and separately derives formulas for actual towers.

## Contents

- `delayed_digit_stabilization.pdf`: complete article.
- `delayed_digit_stabilization.tex`: self-contained LaTeX source and bibliography.
- `code/stabilization.py`: exact valuation, onset, minimum, density, radix, and CRT utilities.
- `code/verify.py`: independent modular-exponentiation checks and regression suite.
- `code/minimal_certificate.py`: tiny, independent counterexample verifier.
- `data/verification.json`: actual test results, counts, certificates, and exact density.
- `data/primary_certificates.csv`: first nonzero residue digits for the counterexample.
- `source_audit.md`: source provenance and distinction between prior work and deductions.
- `short_solution.md`: standalone mathematical answer to the selected question.
- `build.ps1`, `build.sh`: reproduction scripts for Windows and POSIX systems.

## Reproduce the calculations

Python 3.9 or later is sufficient. No third-party Python packages are required.
The included run used Python 3.13.5.

    python code/minimal_certificate.py
    python code/verify.py

The latter rewrites the JSON and CSV data files. Numerical results and counts
are deterministic; the recorded Python version and elapsed time are environment-dependent.

The included run completed 21,997 modular certificates, 100 minimum-table
residue tests, and 20 CRT/idempotent checks. All passed. The general-radix
sweep skipped 1,111 high-valuation cases because of a verification-modulus
cap; this is recorded explicitly in the report, not treated as a passed test.
The mathematical proofs cover all the parameters in their statements.

## Build the PDF

Install a TeX distribution with the packages used in the source, including
newtx, amsmath/amsthm, mathtools, microtype, tcolorbox, listings, xurl, and hyperref.
No external bibliography processor is needed.

On Windows, from PowerShell:

    ./build.ps1

On a POSIX system:

    sh build.sh

The scripts run the exact tests and then pdflatex three times to settle
cross-references and the table of contents.

## Computational scope

The code never constructs a ** (B ** n), but its modular verifier does
construct the much smaller integer exponent B ** n. It is not an arbitrary
symbolic up-arrow evaluator. The function `minimum_failure_spec` returns a
compact (K, coefficient, sign) description when constructing 2**K would be
impractical. Radix factorization is by trial division and intended for small
radices. These implementation limits do not limit the mathematical theorems.

The article provides ordinary mathematical proofs and exact numerical
certificates, not proof-assistant formalization or independent peer review.
The original question was publicly posed in October 2025; its retrieved page
displayed no answers during the check for this note. The source audit makes
no claim to an exhaustive worldwide priority search.
