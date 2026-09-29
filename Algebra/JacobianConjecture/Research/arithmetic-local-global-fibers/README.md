# Arithmetic Local–Global Dichotomies for ProveIt's Three-Variable Keller Map

Research article prepared for Vladimir Reshetnikov, September 24, 2026.

## Read

Open `arithmetic_fibers.pdf`; the complete source is `arithmetic_fibers.tex`.
The bibliography is included in the TeX source, with pinned repository links.

## Principal results proved here

* An explicit infinite family of integral targets with a preimage in every
  Z_p^3 but no preimage in Z^3. Every geometric fiber in this family consists
  of exactly three rational points, whose denominators are displayed.
* A complete gcd classification on the split integer-root plane C=2.
  Locally soluble parameters have density 27/(4*pi^2), and the corresponding
  targets are Zariski dense in that plane. For every fixed finite set S of
  primes, the same parameter density and target Zariski density survive after
  discarding all fibers with an S-integral point.
* An exact integral 2-adic fiber law: probabilities (21,7,3,1)/32 for
  cardinalities 0,1,2,3. Image membership and the fiber cardinality are
  determined modulo 8. The image measure is 11/32. A general inverse-ball
  lemma proves stabilization at every higher precision.
* A contrasting rational Hasse principle over every number field, and an
  elementary quantitative zero-density estimate for rationally soluble
  integral targets.

## Status and attribution

The map, its Jacobian determinant, its complex fiber stratification, and its
finite-field histograms are prior results and are credited as such. The
split integral family, the parameter-density refinements, and the dyadic law
are candidate new results relative to the inspected sources. Global priority
has not been established. This is not a new disproof of the Jacobian
conjecture or a claimed solution of its two-variable case.

The explicit integral counterexamples HAVE rational preimages. They are not
rational Hasse failures, and do not contradict prior degree-five examples
with local points everywhere but no rational point.

The new results have not been formalized or compiled in Lean/Rocq. Mathematical
proofs and exact computational certificates are provided. The dyadic law has
a small finite-enumeration component, with independent pointwise checks and
an analytic proof connecting it to all precisions.

## Reproduce the checks

From this directory, with Python 3.10 or newer:

```sh
python3 code/verify_finite.py --output certificates/finite_checks.json
python3 code/verify_split_plane.py
```

These scripts use only the standard library. For symbolic checks and the
complete rational inverse utility, install SymPy (the executed version was
1.14.0):

```sh
python3 -m pip install sympy==1.14.0
python3 code/verify_symbolic.py
python3 code/rational_inverse.py 0 -4 2
python3 code/rational_inverse.py 0 1 0
python3 code/rational_inverse.py 4/27 4/3 1
```

The last example is an empty geometric fiber. Inputs are exact integers,
fractions, or finite decimals; they are not evaluated as Python expressions.

`code/verify_finite.py` also exports `congruence_preimage(n, modulus)`, which
constructs an integer source attaining the family target modulo any positive
modulus. Its factorization routine is elementary trial division, intended
for moderate moduli rather than cryptographic-size inputs.

## Build the PDF

A full TeX Live installation with New TX fonts and the listed standard
packages is sufficient. No shell escape or external figures are required.

```sh
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_fibers.tex
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_fibers.tex
pdflatex -interaction=nonstopmode -halt-on-error arithmetic_fibers.tex
```

An additional run is useful when the table of contents changes pagination.
The delivered PDF was rendered and visually checked.

## Contents

* `arithmetic_fibers.tex`, `arithmetic_fibers.pdf`: article.
* `code/`: exact checkers and rational inverse utility.
* `certificates/`: actual execution logs and machine-readable tables.
* `SOURCE_REVIEW.md`: prior-work review, pinned references, and limitations.

No third-party PDFs or font files are included. The scripts do not modify
any repository, contact external services, or mutate the user's files.
