# Mollweide, tangent laws, and power of a point in intuitionistic PRA

This packet gives a fully developed human-readable constructive proof of:

1. Mollweide's two formulas;
2. the law of tangents;
3. the law of cotangents and its inradius formula;
4. the power-of-a-point theorem;
5. the tangent-secant theorem;
6. the intersecting chords theorem;
7. the intersecting secants theorem.

## Start here

- `mollweide_circle_ipra.pdf` - compiled 25-page report.
- `mollweide_circle_ipra.tex` - complete LaTeX source.
- `lean/IPRAFormalizationPlan.md` - clear route to a complete internal Lean/iPRA formalization.
- `verification/certificate_report.txt` - captured output of 30 exact checks.
- `verification/results.json` - machine-readable check ledger.

## Main mathematical idea

The triangle results are reduced to a positive half-angle certificate. With

```text
x = s-a,  y = s-b,  z = s-c,
a = y+z,  b = z+x,  c = x+y,
```

the positive half-angle components are defined by six square equations. Four
positive-root product identities prove the complement relation among the three
half-angles. Two ring identities then give the denominator-free Mollweide
formulas, from which the tangent law follows. The cotangent law is the single
cross equation

```text
r*cos(A/2) = (s-a)*sin(A/2).
```

For circles, every theorem is a corollary of one quadratic identity. Along a
line `P+tV`, power is `p+2*h*t+q*t^2`. For two apart roots `u,w`,

```text
w*f(u) - u*f(w) = (w-u)*(p-q*u*w),
```

so constructive cancellation yields `p=q*u*w`. External secants, internal
chords, and tangents are order/sign specializations.

## What "in iPRA" means

First-order intuitionistic primitive recursive arithmetic has numerical
variables, not a sort of all real numbers. The report therefore gives:

- uniform finite statements for natural-number codes of rational data and
  finite certificates; and
- a first-order theorem schema for each fixed tuple of primitive-recursive
  regular-name programs.

Division and cancellation require explicit apartness witnesses. No witness is
extracted from a bare negated equality. All induction is on quantifier-free
invariants of bounded algorithms.

## Lean contents and status

- `lean/AlgebraicCore.lean` - proposed ambient Mathlib ring certificates.
- `lean/ConstructiveCorollaries.lean` - proposed ordered-field quotient and
  cancellation corollaries.
- `lean/ObjectTargets.lean` - exact `ConciseIPRA.PRAAx` target shape and native
  transport interface.
- `lean/IPRAFormalizationPlan.md` - module-by-module completion plan.
- `lean/FORMALIZATION_STATUS.txt` - explicit status boundary.

Neither `lean` nor `lake` was installed in the delivery environment. The Lean
sources contain no `sorry`, but were not compiled, and no completed internal
`Prf PRAAx` proof object is claimed. An ambient Mathlib ring proof is not by
itself an iPRA derivation.

The object-language plan targets ProveIt commit:

```text
948fe06760595e3bce468b67d25032bbbf7f376d
```

## Executed verification

The exact Python/SymPy audit passed all 30 checks. It covers the half-angle
bridge, both Mollweide identities, the tangent law, the cotangent/inradius
certificate, the power-line quadratic, secant factorization, tangent residual,
and exact rational examples.

The PDF was compiled with `latexmk`, rendered page-by-page at 180 DPI, and
visually inspected. PDF preflight found it openable, unencrypted, text-based,
and free of suspicious structure. All fonts are embedded.

These checks support the development; they are not substitutes for the future
embedded iPRA proof objects.

## Reproduce

Requirements:

- Python 3;
- SymPy 1.14 or compatible;
- a normal TeX Live installation with `latexmk` and `pdflatex`.

Run:

```bash
bash build.sh
```

The final checker line must be:

```text
ALL CERTIFICATES PASS (30 checks)
```

## Layout

```text
mollweide_circle_ipra.tex
mollweide_circle_ipra.pdf
README.md
build.sh
requirements.txt
lean/
sources/
verification/
```

Prepared for Vladimir Reshetnikov, 15 November 2026.
