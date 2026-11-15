# Heron, sine, and cosine laws in intuitionistic PRA

This package contains a complete human-readable mathematical argument,
explicit finite arithmetic versions of the three formulas, exact executable
checks, and a concrete Lean completion plan.

## Start here

- **triangle_formulas_ipra.pdf**: the full report.
- **triangle_formulas_ipra.tex**: its complete LaTeX source.
- **lean/OUTLINE.md**: formalization stages and actual ProveIt API.
- **verification/results.json**: executed exact-arithmetic checks.

The proof gives the radical form of Heron's formula, all three cosine laws,
and the extended sine law including 2R. It constructs the circumcenter
explicitly. Geometric sine and cosine are the standard normalized unit-ray
coordinates; an independently defined analytic radians API is not assumed.

## What “in iPRA” means

First-order iPRA has numerical variables, not a sort of all real numbers.
The report proves uniform numerical statements for coded rational
coordinates and precision inputs, and a first-order schema for every fixed
tuple of primitive-recursive coordinate-name programs. It includes the
regular-name arithmetic, a bounded root algorithm, reciprocal separation
bounds, and a quantifier-free induction audit.

Heron includes degenerate triangles. The divided sine law and circumcircle
require a positive determinant-apartness witness; the proof does not infer
such a witness from merely negating equality to zero.

## Formalization status

**No Lean compilation was performed.** Neither Lean nor Lake is installed
in the delivery environment. The .lean files are proposed proof scripts,
executable definitions, and explicit proposition/derivability targets.
The full internal iPRA formalization remains to be implemented.

- FiniteAlgebra.lean and RationalAlgebra.lean contain concrete algebraic
  proof scripts with no added axioms or unfinished proof placeholders.
  They are still uncompiled.
- DyadicSpec.lean specifies the root program and its missing correctness
  proof.
- FiniteTargets.lean states the exact finite Heron and trigonometric
  propositions from the report. It does not prove them.
- ObjectTargets.lean uses the inspected ConciseIPRA syntax to specify
  internal derivability and conditional native transport. The particular PR
  codes and their derivations have not been constructed.

An ambient Lean ring proof is not by itself an iPRA derivation. The report
and completion plan explicitly retain this boundary.

## Exact computations executed

The standard-library Python checks passed:

| Check | Count |
|---|---:|
| Fixed polynomial identities | 15 |
| Rational square-root brackets | 3696 |
| Bounded binary root vs literal scan | 140 |
| Finite radical-Heron instances | 144 |
| Finite cosine and extended-sine instances | 132 |

They include obtuse, clockwise, very thin, collinear, coincident, and zero
triples, and use exact integer/Fraction arithmetic throughout. These checks
support the implementation and constants; they are not formal proof.

## Reproduce

With Python 3 and a normal TeX Live installation:

    bash build.sh

Or run the numerical checks alone:

    python3 python/verify.py

The report uses ordinary LaTeX packages including amsmath, amsthm,
Latin Modern, microtype, TikZ, booktabs, and hyperref. The PDF is compiled from
the supplied source.

For the proposed Lean scripts, use a configured checkout of the pinned
ProveIt revision and the commands in lean/OUTLINE.md. The included
toolchain pin is leanprover/lean4:v4.32.0; the inspected Mathlib requirement
is v4.32.0. The object-language file depends on ProveIt's ConciseIPRA
modules, while the finite algebra files need only Mathlib.

## Repository basis

Inspected ProveIt commit:

    38cafaa5be7f4602567440bcebc754abdbacefc9

sources/manifest.json records pinned source URLs and their roles.
Existing surreal geometry supplies relevant algebraic proof patterns;
none of its ambient field or analysis infrastructure is treated as an
already completed iPRA construction. No consistency theorem is needed.

## Package layout

    triangle_formulas_ipra.tex
    triangle_formulas_ipra.pdf
    build.sh
    lean/
    python/
    sources/manifest.json
    verification/results.json
    verification/numerical_checks.txt
    verification/mathematical_review.txt
    verification/latex_final_1.log
    verification/latex_final_2.log
    verification/pdf_quality.json
    SHA256SUMS

Prepared for Vladimir Reshetnikov, 14 November 2026.
