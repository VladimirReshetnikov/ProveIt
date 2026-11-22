# Exact rational implicit-function demonstrator

This directory supplies a reproducible reference implementation and targeted
finite validation of the paper's approximation scheme. It is not an iPRA
derivation or a complete Lean formalization. The universal hypotheses for the
examples are proved in the paper; checking a finite sample does not prove them.

## Run

From the package directory:

```sh
python3 code/validate.py
```

Only the Python standard library is required. The command writes
`validation/python_validation.json`. All assertions use exact integers and
`fractions.Fraction`; floating point plays no role in pass/fail decisions.
The JSON is deterministic, including hashes of the two Python source files.

## Solver

`implicit_solver.py` implements one fixed rational provider at a time. Its
`solve` routine starts at the supplied rational center. At demand `k`, it uses
precision `p = k+5`, floors each update to the dyadic grid of that precision,
and clips each coordinate to its rational interval. It performs exactly
`N = k+s+4` updates, where `s` is the least nonnegative exponent with
`2*r <= 2**s`. The search for `s` has the explicit finite bound given by the
numerator of `2*r`. There is no tolerance-based stopping loop.

Four evaluator modes are provided: exact values, the largest permitted
positive error, the largest permitted negative error, and deterministic
input-dependent error signs. All satisfy the declared rational error bound.
The callback interface is ordinary executable reference code. It makes no
claim to interpret every primitive recursive source program in iPRA.

## Examples

* The circle is presented by `H(x,y) = (x*x+y*y-1)/2`, around `(0,1)`,
  with root radius `1/4` and parameter radius `1/4`.
* The coupled polynomial system is
  `H1 = y1+y1*y2/4-x`, `H2 = y2+y1*y1/4-x/2`, around the origin,
  with root radius `1/4` and parameter radius `1/16`.

Both examples use the paper's general half-contraction bound. Their actual
derivative contraction bounds are the sharper `1/4` and `1/8` respectively.

## What is checked

The suite runs both examples at nine parameter values, every demand from
`0` through `64`, and all four oracle modes. It verifies the fixed clock,
the oracle error, negative and positive dyadic flooring, domain preservation,
each inexact step, and the terminal residual bound.

Coarse traces are compared with the final segment of finer traces. Checks
cover the one-step recurrence, its denominator-cleared finite invariant,
the pairwise Cauchy estimate, and the estimate for perturbed parameters.
Separate edge cases force clipping at both ends of a non-dyadic interval.
The circle output is also compared with an independently computed rational
square-root bracket using `math.isqrt`.

Finite Neumann sums are checked on both sides of the matrix identity, including
zero terms. Their derivative approximants are compared with an independent
exact rational Gaussian elimination result. Exact polynomial Taylor identities
and a finite derivative remainder bound are checked on nearby computed points.
Gaussian elimination here only checks rational matrices at finite samples;
the paper constructs inverses of represented matrices through finite Neumann
approximants instead.
