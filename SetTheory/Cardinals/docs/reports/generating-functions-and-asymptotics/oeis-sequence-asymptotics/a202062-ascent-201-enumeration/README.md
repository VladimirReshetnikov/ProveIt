# Exact enumeration of 201 avoiding ascent sequences

This package contains a self-contained proof of the cubic generating function
conjectured by Guttmann and Kotešovec for OEIS A202062, together with rigorous
all-orders coefficient asymptotics and an inverse expansion. Their original
generating-function conjecture and leading asymptotic are credited in the report.

## Files

- `a202062-report.pdf`: complete mathematical report
- `a202062-report.tex`: editable source, including the entire proof
- `verify_exact.py`: dependency-free-data exact algebra certificate
- `puiseux.py`: exact number-field coefficient generator
- `inverse.py`: arbitrary-order inverse coefficients and a numerical log-target illustration
- `enumerate_sequences.py`: independent finite-word checks and tree counts
- `build.sh`: reproducible PDF build
- `requirements.txt`: Python dependency
- `certificate-output.txt`, `puiseux-results.txt`, `relative-coefficients.txt`:
  recorded exact results

## Reproduce the mathematics

Use Python 3 with SymPy installed:

    python verify_exact.py
    python puiseux.py --relative-order 5
    python inverse.py --order 5 --target-log 1000
    python enumerate_sequences.py --check-length 8 --terms 40

The first command asserts every displayed finite algebraic reduction, including
the rational invariant, trace, parameterization, generating-function cubic and
correctly signed comparison to the original conjecture. It prints one PASS line.
The second uses exact arithmetic in the relevant algebraic number field and
checks cancellation of the first three odd Puiseux powers before producing
arbitrary fixed-order relative corrections. The inverse command checks the formal residual exactly and illustrates the real approximation without asserting an exact integer threshold. The enumeration command is a separate diagnostic;
finite initial agreement is not used as proof.

## Build the report

    bash build.sh

A standard TeX Live installation with AMS packages, geometry, hyperref, enumitem,
microtype and Latin Modern fonts is sufficient. The script also supports a
minimal Linux installation with the TeX source tree present but no filename
cache or prebuilt format. Generated build files stay in `.build`.

## Interpretation of the inverse

The report specifies a positive cut-integral model before defining a real inverse.
Its all-orders expansion agrees with the sequence up to an exponentially smaller
error. The integer threshold is bounded using ceilings with explicit asymptotic
error scales; an unqualified exact rounding formula is not claimed. Numerical
bounds at a particular finite threshold require additional explicit constants.

## Source comparison

The conjectured cubic is equation (3.1) of Guttmann--Kotešovec (2023). Their final
printed combination of its algebraic and rational parts has a sign error; the
corrected affine substitution is documented and checked exactly in the report.
No alteration of their conjectured cubic is required.

The package is a reproducible research result, not a claim of journal peer review.
The report distinguishes the proved A202062 result from the still-conjectural
subexponential factors for 120-avoiding ascent sequences.
