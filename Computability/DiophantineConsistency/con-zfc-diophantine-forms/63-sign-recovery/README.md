# Recovering signs and absorbing Pell quotients

**Three explicit Diophantine consistency constructions for ProveIt.**
Prepared 23 October 2026 against repository commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`.

The complete manuscript is [`report/report.pdf`](report/report.pdf), with
editable LaTeX in [`report/report.tex`](report/report.tex) and the two
component `section.tex` files. The mathematical target is syntactic
consistency of ZFC. On each stated domain, absence of zeros is equivalent
to `Con(ZFC)` by the new arguments composed with the explicitly identified
inherited compiler, calibration, and Pell/ratio theorems.

## Results

| Construction | Domain | Variables | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| Source 57 quartic | unrestricted integers | 45 | 4 | not optimized |
| **New Q42** | **unrestricted integers** | **42** | **4** | not optimized |
| Sources 55/59 positive form | strictly positive integers | 14 | 52 | 79 |
| **New P14** | **strictly positive integers** | **14** | **34** | **87** |
| Source 59 free-coordinate form | strictly positive integers | 9 | 1,910,404 | 473 |
| **New F9** | **strictly positive integers** | **9** | **1,573,266** | **504** |

These improve different complexity measures. Q42 saves three integer
unknowns without increasing degree. P14 lowers degree by 34.62% for eight
additional operations. F9 lowers degree by 17.647% for 31 additional
operations. No global optimum or simultaneous dominance is asserted.
Source 58's 15-positive degree-24 / 90-operation equation and source 51's
15-positive degree-157 / 66-operation equation remain useful alternatives.

An arithmetic operation means one live binary addition, subtraction, or
multiplication; register reuse and fixed integer leaves are free. This is
not a bit-complexity measure. Every displayed exponent is fixed. Implicit
registers are polynomial abbreviations, except where Q42 explicitly counts
them as constrained supplied unknowns.

## The main new ideas

1. **Recover two signs from one product.** Replace separate ternary
   representations of positive eta and zeta by a single representation of
   their positive product. Strengthen the old square restriction from
   `w=u^2` to `w=4u^2`. This preserves canonical accepting witnesses and
   gives `|E|>3R+1`. The negative common-sign branch forces a first Pell
   index larger than R, while the auxiliary norm forces the main index to
   equal R. Monotonicity excludes that branch. The resulting polynomial
   is the sum of squares of **27 quadratic residuals** in **42 integers**;
   its coefficient of `tau^4` is exactly one.

2. **Absorb a quotient into an existing root carrier.** In the positive
   construction, the main root is represented by
   `D=b0+H(t-(k-R-1)/(4q^4))`. Clearing the denominator in a square equation
   removes the old quotient h. An early bound excludes first Pell index
   one before h is reconstructed, avoiding a circular recovery argument.
   Five residuals of degrees `12,17,2,16,15` give the degree-34 sum of squares.

3. **Deflate a polynomial majorant using a parameter identity.** The
   nine-variable component exploits `e^2=16i^2 D-i^2 W` in the ratio
   construction before taking a higher square-root approximant. Its
   universal strict majorant is certified by an exact **264-term**
   positive-coefficient expansion. A separate two-defect identity proves
   the lower exact degree of the unchanged style of final norm equation.

## Contents and coefficient binding

- `quartic/`: the literal 42-variable residual system, exact symbolic
  expanded polynomial, builder/verifier, and finite audit.
- `positive14/`: the 87-operation primary circuit, degree certificate,
  proof, verifier, natural-number translation, and LaTeX section.
- `nine/`: the frozen nine-positive circuit, its exact majorant certificate,
  source data, complete coefficient binding, proofs, independent checker,
  and nonnegative-domain translation.
- `coefficients/`: the **whole source-34** four-integer tuple used by Q42
  and P14, including actual binary payloads, compressed payloads, a finite
  builder from the 430 literal machine actions and 943 tiles, and an
  independent decoder. Here `beta=2^1064921-1`; the `MF_source` payload is
  already shifted. Do not shift it again or mix ports between tuples.
- `upstream/`, `provenance/`: unchanged inherited proof material, licenses,
  and pinned file identities. The nine-variable component has its own
  complete source binding; use that component's coefficients with it.
- `reviews/`: separate internal mathematical reviews of the new steps.
- `VERIFICATION.json`, `MANIFEST.sha256`: release verification receipt and
  hashes of the supplied artifacts.

All constants are completely fixed by finite data and recipes. No open
program-index parameter or coefficient defined by searching for a ZFC
refutation occurs. The large coefficient payloads are fixed constants,
not additional existential variables.

## Reproduction

Python 3.10 or later is sufficient; the verification programs use only
the standard library. From this directory:

```sh
python3 verify.py
```

The driver authenticates the release manifest and the pinned inherited
files, rebuilds the main coefficient tuple in a temporary directory and
compares the raw bytes, runs the independent coefficient decoder, checks
all three literal constructions, and runs the independent majorant
checker. It also reruns the new quartic and P14 checks with Python's
assertion optimization enabled. The inherited coefficient tools explicitly
require ordinary Python mode and are invoked accordingly.

The checks certify identities, coefficient bindings, counts, finite data,
and exact degrees. Finite modular comparisons and small sign tests are
diagnostics, not a proof of the unbounded solvability equivalence. That
equivalence is established by the manuscript's ordinary mathematical
arguments and the inherited theorems named there.

To rebuild the manuscript with a standard TeX Live installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The release manifest authenticates the delivered PDF. A locally recompiled
PDF can have different metadata bytes, so regenerate a manifest when
creating a new release rather than expecting the old PDF hash to match.

## Proof status and integration

This package provides ordinary mathematical proofs of the new reductions
and reproducible finite arithmetic certificates. It does **not** provide
a newly compiled end-to-end Lean/Rocq semantic theorem or a derivation in
the repository's object-language ZFC calculus. The preserved
`upstream/OBJECT_ZFC_STATUS.md` describes that formalization boundary.
The report separately explains why the uniform coded arguments can be
carried out in ordinary ZFC; it does not infer internal provability merely
from an external Lean equivalence. The inherited ordinary K215 proof is
retained verbatim, and `reviews/ZFC_INTERNALIZATION_SCOPE.md` identifies
the set-model constructions and their exact source interfaces.
Internal mathematical reviews were performed independently of the
corresponding builders; they are not external peer review.

For repository incorporation, retain the folder as one self-contained
package and add links to the three measured frontier points. The snapshot
already contains packages 54–59 even though the collection's top-level
comparison still describes wave 7. Choose the next package number only
at integration time. Do not replace lower-cost or lower-degree points
that these constructions do not dominate.

See `NOTICE.md` for attribution and inherited licenses. Neither the ZIP
nor its verification attempts to decide consistency or search for a zero.
