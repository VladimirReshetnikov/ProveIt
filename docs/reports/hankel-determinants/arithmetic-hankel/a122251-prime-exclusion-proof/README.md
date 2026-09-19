# Arithmetic Hankel determinants: an OEIS conjecture attack

The selected conjecture is the general-prime numerator formula recorded in
OEIS A122251. A122249 is its binary special case. The formula is proved,
not refuted, in `report.pdf` (13 pages), with source in `report.tex`.

## Main result

For positive integers d,b with gcd(d,b)=1 and matrix size m >= 0, let

    D_m(d,b) = det(1 / (b + d*(i+j))) for 0 <= i,j < m.

Then its numerator in lowest terms is

    product over prime ell dividing d of
        ell ** (v_ell(d)*m*(m-1) + 2*sum(v_ell(j!), j=0..m-1)).

This is independent of b and is a perfect square. For a prime step p and
OEIS index n=m-1 it equals

    (p*p) ** sum(floor(k / p**a), k=1..n, a>=0).

The proof separately rules out every prime other than p; merely finding
the p-adic valuation would not have sufficed.

## Further proved results

The article determines every reduced denominator valuation. It also proves
that the gcd of the denominators over all positive b coprime to d is the
largest divisor coprime to d of

    H_m = product((2*j+1) * binomial(2*j,j)**2, j=0..m-1).

This gcd is achieved by denominators at only two explicitly constructed
shifts. There are additional results for inverse-matrix denominators,
unequal arithmetic steps, and noncoprime parameters. Exact counterexamples
show why several tempting unqualified extensions are false. Those are not
counterexamples to the recorded OEIS conjecture.

## Reproduce the computations

Python 3.10 or later; standard library only. From this directory:

    python3 code/verify.py

The script is also callable by its absolute path. It uses only exact
integers and `fractions.Fraction`. It regenerates the files in `data/`.
The run supplied with this package used Python 3.13.5 and passed every
check, including 3,231 direct primitive determinants, 35,244 product-ratio
cases, 20,240 local denominator valuations, 180 constructed gcd
certificates, and 720 full inverse matrices. These ranges overlap; do not
add them as though they were disjoint observations.

The calculations audit the formulas and implementation. They do not replace
the proofs or establish all cases by finite search. No proof-assistant
formalization is claimed.

## Rebuild the PDF

On a TeX installation with pdflatex and the packages in the preamble:

    sh build.sh

The build uses standard TeX packages, including newtxtext/newtxmath,
amsthm, mathtools, microtype, tcolorbox, xurl, and hyperref. Font files are
not distributed. `build.sh` places intermediates in `.build/` and copies
the final PDF to `report.pdf`.

## Files

- `report.tex`, `report.pdf`: complete article and proofs.
- `code/arithmetic_hankel.py`: documented exact arithmetic library.
- `code/verify.py`: independently computed regression and theorem audits.
- `data/verification_summary.json` and `.txt`: recorded executed results.
- `data/oeis_numerators.csv`: formula-generated terms for n=0..35 and
  d=2,3,4,5,6,10,12; matrix size m is also recorded.
- `data/small_determinants.csv`: exact directly evaluated sample determinants.
- `data/gcd_certificates.json`: selected constructed two-shift certificates.
  Large denominator values are stored as decimal strings for portability.
- `notes/source_status.md`: checked sources and priority qualification.
- `notes/oeis_submission.txt`: draft contribution text; not submitted.
- `build.sh`: reproducible two-pass LaTeX build.

## Status and priority

The OEIS pages consulted still label the relevant claims as conjectural.
The note gives a self-contained proof of those claims as written and of
the stated extensions. It does not certify global novelty or establish
that equivalent results are absent from the literature. Cauchy's determinant
identity and the inverse Hilbert determinant are explicitly credited as
classical. No OEIS edit, journal submission, or other external write was made.
