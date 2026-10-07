# Report183: exact computational supplement

This supplement reproduces the finite computational certificates for the
A394326 asymptotic theorem. The report supplies the analytic arguments connecting
these finite checks to the infinite trace-class operators and to the original
hard-rod extraction. The executable checks do not replace those arguments.

## Quick start

Requires Python 3.10 or newer. The complete default replay uses **only the Python
standard library**. It needs no network, compiler, SymPy, mpmath, NumPy, OEIS
access, research workspace, or system LaTeX installation.

From the extracted report directory:

```sh
python reproduce.py
```

This runs all certificates and tests twice, normally and with `-O`, with `-I -S -B`
isolation, no site-package imports, and no bytecode writes. The child environment
is fixed; inherited `PYTHONPATH` and Python startup hooks cannot affect replay. It compares every JSON output byte for byte with
the supplied references and with the other mode. By default, replay
outputs are created in a temporary directory outside the extracted package and
removed afterward, preserving its manifest. Pass `--output-dir PATH` to retain
them in a chosen directory. A failure exits nonzero.
All mathematical acceptance conditions use explicit exceptions; none is a
removable `assert` statement.

The full two-mode replay took approximately 36 seconds in the preparation
container (Python 3.12.14). Runtime depends on hardware and Python version.
The four input data files occupy approximately 1.4 MB. Output JSON contains no
wall-clock times, absolute paths, or optimization-mode-dependent fields.

For a single run without comparing with frozen references:

```sh
python -S code/run_all.py --output-dir build/single
python -S -O code/run_all.py --output-dir build/optimized
```

These commands regenerate eleven deterministic JSON files. `summary.json`
records their hashes and the hashes of every Python source in `code/` and all
input JSON data. The final report archive's manifest separately binds the
manuscript and top-level files.

## What is checked

1. **Exact coefficients.** The primary generator enumerates nonnegative-deficit
   gap paths up to their first return. The proven support bound `W >= m-1`
   makes the weight-65 cutoff exact. It obtains `C=1-1/I` by integer reciprocal
   arithmetic and reproduces 40 displayed source terms. Terms 41 through 65 are
   independently generated extensions, not an assertion of b-file verification.
   A separate full-tableau dynamic program uses ordinary row-word inversions,
   reverses the finite polynomials, checks hook-length totals through size 9,
   and independently extracts the hard-rod span coefficients through weight 8.
2. **Genuine finite determinant.** The ungauged 14-state matrix has a Leibniz
   degree bound of 239. Exact Bareiss determinants at all 240 integer arguments
   prove the supplied degree-161 polynomial is the genuine determinant.
   The polynomial is also regenerated from scratch by exact Newton forward
   interpolation. A separate Fraction Gaussian-elimination implementation
   checks all 240 values again. No symbolic algebra library is required.
3. **Polynomial adjugate and structure.** Every coefficient in the full identity
   `(I-L_8(z))*Adj_8(z)=N_8(z^2)*I` is checked. The complete ordered core, signed
   exceptional row, finite gauge identities, cross-block support, derivative
   majorant and infinite-tail bounds are verified. An adversarial common factor
   multiplying both adjugate and denominator passes the adjugate identity but
   fails the independent genuine-determinant check.
4. **Global circle.** All 8192 rational nodes lie exactly on `|q|=63/100`.
   Integer complex Horner arithmetic certifies their moduli and a polygonal
   winding number of one. The derivative majorant and rational mesh spacing
   give the whole-circle lower bound `323/12800`; the proof uses the more
   conservative `2/125` for its stated Schur bound. The independent checker
   uses Fraction forward power sums at 22 selected nodes and three ray
   orientations. The negative-ray count explicitly exercises the closing edge.
5. **Real bracket and noncancellation.** Outward dyadic arithmetic at 220 bits
   verifies the height-20 numerator signs at `z=0.78615504, 0.78615506`, the
   denominator's negative sign throughout that interval, inverse residuals,
   and tail Schur contractions. There are 76 numerator states and 77 denominator
   states. Squaring the endpoints gives the certified rho bracket.
6. **Residue and amplitude.** Finite solves are certified by exact residuals;
   differentiated tail and Schur bounds extend the derivative enclosure to
   the infinite operator. The amplitude is rigorously enclosed by
   `0.1838102868 < c < 0.1838120734`.
7. **Remainder and inverse consequences.** Exact rational inequalities establish
   the full circle resolvent bound 525, the generating-function bound 2400,
   and the coefficient bound `2500*(100/63)^n`. They also verify exclusion of
   the golden growth constant, the signed limiting Fibonacci residual,
   positivity and strict increase for every `n>=600`, and the exact integer
   prefix bound `Y0`. Formal series reversion checks the signs and coefficients
   of both envelope-inverse series through order eight at four rational alpha
   values. The all-order formula is proved analytically in the report.

`certificates/tests_global.json`, `tests_local.json`, and
`tests_coefficients.json` contain 39 test groups, including randomized exact
small cases with fixed seeds and deliberate corruptions. Examples include a
permuted core, altered polynomial or adjugate coefficients, an extraneous common
factor, off-circle nodes, reversed contour orientation, zero or corrupted
inverse proposals, invalid precision, and bounds too weak to justify `n=600`.

## Source and output inventory

- `code/exact_coefficients.py`: integer coefficient generator and independent
  finite-tableau/span checks
- `code/certify_rational_circle.py`: exact global finite/infinite certificate
- `code/independent_global_check.py`: independent determinant, node and winding
  checks
- `code/regenerate_polynomial.py`: exact standard-library reconstruction of N8
- `code/rigorous.py`: outward dyadic arithmetic, operator construction, exact
  residual verification and optional candidate generation
- `code/certify_local.py`: real signs, noncancellation and residue enclosure
- `code/certify_consequences.py`: remainder, non-golden and inverse consequences
- `code/test_*.py`: corruption and arithmetic tests
- `code/run_all.py`: all checks and deterministic output generation
- `code/generate_proposals.py`: optional approximate inverse proposal regeneration
- `data/N_H8.json`: exact degree-161 polynomial
- `data/adjugate_H8.json`: exact polynomial adjugate, denominator and ordered states
- `data/inverse_proposals.json`: three dyadic point matrices, all exactly
  residual-checked on every replay
- `data/exact_coefficients.json`: coefficients `a(0)..a(65)`, first-return
  coefficients, independent prefix evidence and source provenance
- `certificates/global.json`, `global_independent.json`,
  `polynomial_regeneration.json`, `local.json`, `remainder.json`, `inverse.json`,
  `coefficients.json`, `tests_global.json`, `tests_local.json`,
  `tests_coefficients.json`, `summary.json`: frozen expected outputs

Standalone scripts with output options may be run from any working directory;
they locate their inputs relative to their own locations, not to the current
working directory. The complete directory can be relocated without edits.

## Optional inverse proposal regeneration

The frozen matrices are **candidates**, not trusted enclosures of inverses.
For each interval matrix A, the exact check proves `||I-B*A||<1` and obtains
`||A^-1|| <= ||B||/(1-||I-B*A||)`. Candidate rounding errors therefore cannot
invalidate a successful certificate. Linear solves also verify their residuals.

Only optional regeneration of those candidates imports mpmath, inside
`rigorous.propose_inverse`. Preparation used mpmath 1.3.0 at 80 decimal digits.
If already available, regenerate to a new file with:

```sh
python code/generate_proposals.py --output build/new_inverse_proposals.json
```

The output parent directory must exist. Every candidate is residual-checked
before writing. Default replay never imports mpmath and uses no mpmath interval
arithmetic. A different valid proposal may change exact output endpoints or
hashes; it does not have to reproduce the frozen proposal bit for bit. To adopt
new proposals, replace the data file, rerun all checks, review the resulting
bounds, and regenerate the reference outputs together. Do not simply alter a
hash to suppress a failed mathematical check.

The exact finite polynomial can be regenerated independently with:

```sh
python -S code/regenerate_polynomial.py --output build/new_N_H8.json
```

Its JSON formatting differs from the compact input file; compare parsed objects.
The all-check runner performs that comparison automatically. The supplied
adjugate is proof data checked by its exact identity plus the separately proved
genuine determinant identity; no unverified common polynomial factor is accepted.

## Scope and provenance

The source definition is credited to Morten Brydensholt's
[OEIS A394326 record](https://oeis.org/A394326). Sean A. Irvine's
[jOEIS translation](https://github.com/archmageirvine/joeis/blob/master/src/irvine/oeis/a394/A394326.java)
was inspected as an executable specification (blob
`e59ad7a42e0c96f832b97b6457ea9b5cb1d4a851`). It is not executed or redistributed
here. The independently written coefficient generator records the source URLs
and inspection date in its JSON provenance.

These certificates locate only the dominant pole. The report's finite spectral
expansion at any fixed zero-free radius below one, higher-order inverse
statements, and span-marker perturbation are structural results. No table of
additional poles, numerical marker neighborhood, all-index positivity theorem,
probabilistic limit law, or worldwide-priority assertion is certified by these
programs. The strict asymptotic equivalents involving the golden ratio are
excluded; a small finite relative Fibonacci residual remains compatible with
the theorem.
