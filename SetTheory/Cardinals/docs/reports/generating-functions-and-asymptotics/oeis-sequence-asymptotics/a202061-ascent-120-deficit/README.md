# Logarithmic deficit of 120 avoiding ascent sequences

This package proves the two-sided order

    n log(mu) - log(a_n) = Theta(n^(1/3) (log n)^(2/3))

for a_n = OEIS A202061(n), where mu = 7.295896943239772... is the largest root
of mu^3 - 8 mu^2 + 5 mu + 1. It also proves the corresponding positive
inverse-threshold correction and non-D-finiteness of the ordinary generating
function.

This excludes the previously estimated pure negative n^(3/8) stretch, and a
pure negative constant-times-n^(1/3) stretch, even with a fixed polynomial
prefactor. It does not determine an exact stretch constant or asymptotic
equivalent, a full transseries, an all-orders inverse expansion, or an
explicit finite-size crossover threshold. Independent mathematical audit and
exact diagnostics are included; this is not formal verification or journal
peer review. Publication priority has not been established.

## Main files

- `a202061-report.pdf`: the standalone mathematical report
- `a202061-report.tex`: editable LaTeX source, containing the complete proof
- `build.sh`: reproducible PDF build
- `verify_all.sh`: run all author-side mathematical diagnostics
- `critical_certificate.py`: exact critical-point identities and rational intervals
- `block_formula.py`: positive binomial coefficients and operator comparison
- `state_search.py`: normalized suffix recurrence used by the checks
- `check_operators.py`: state/operator coefficient comparison
- `check_height_walk.py`: independent positive height walk versus normalized states and OEIS
- `check_word_states.py`: literal-word validation of every transition through length 10
- `check_narayana.py`: fixed-gap polynomial transformation checks
- `check_staircase.py`: integer lengths, boundaries, binomial admissibility and tilt cancellation
- `audit/`: independent audit, standalone independent tests, and recorded outputs
- `derivation/`: the six original mathematical proof notes and scoped source comparison
- `SHA256SUMS`: hashes of the released files

The original derivation notes retain their historical draft labels. The
standalone report and the final audit state the current mathematical result.
The independently audited source-note hashes can be checked against the
files in `derivation/` using `audit/source-sha256.txt`.

## Reproduce the mathematics

Use Python 3 with SymPy and mpmath installed:

    bash verify_all.sh
    python audit/independent_checks.py
    python audit/staircase_checks.py

All tests are local and use no downloaded data. The OEIS initial terms are
embedded solely for diagnostic comparison. They are not assumptions in the
asymptotic proof. `verify_all.sh` prints the results and does not modify the
recorded release outputs. The independent staircase check is deliberately
more extensive and may take longer than the other tests.

The certificate proves exact algebraic equalities by polynomial reduction,
and strict sign margins by rational interval arithmetic. High-precision
decimal values are labels only. Finite checks do not establish a uniform
asymptotic claim; the report supplies the necessary uniform proofs.

## Build and integrity checks

    bash build.sh
    sha256sum -c SHA256SUMS
    (cd derivation && sha256sum -c ../audit/source-sha256.txt)

A standard TeX Live installation with AMS packages, geometry, hyperref,
microtype and Latin Modern fonts is sufficient. Generated build files stay
in `.build`. The script also supports a minimal Linux TeX tree without a
prebuilt format or filename cache. A regenerated PDF can have different
metadata, so the PDF hash is a check of the supplied release bytes, not a
promise of byte-identical PDFs across TeX installations.

## Attribution and source scope

The class and initial terms are OEIS A202061:
https://oeis.org/A202061

The pure n^(3/8) stretch is a numerical estimate in Conway, Conway, Elvey Price
and Guttmann (2022), not a proved asymptotic:
https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/

The non-D-finiteness proof uses the arithmetic G-function regularity theorem,
as stated in Garoufalidis--Bellissard, Definition 2.2 and Theorem 2.1(c):
https://people.mpim-bonn.mpg.de/stavros/publications/algebraicGfunctions.pdf

The proof here does not assume all D-finite functions have regular singular
points. It uses the integer coefficients and exponential growth bound to
invoke G-function regularity, then smoothness at the radius and Pringsheim's
theorem.
