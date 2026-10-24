# Congruence, radical norms, and direct proof certificates for Con(ZFC)

Research package prepared for Vladimir Reshetnikov's ProveIt project.
Comparison snapshot: `a88aefd7ddab4771534bb049c67350e397c91b9a`.
Prepared 24 October 2026.

Start with **report/report.pdf**. Its complete editable LaTeX sources are in
the same directory. The article supplies definitions, proofs, exact degree
certificates, comparisons, explicit dependency boundaries, and further questions.

## Main result: 16 unrestricted integers, degree 124, 118 operations

The recommended modest-degree polynomial is

    P16 = (1 + N2) * Ff * Fg * Ft - 1,
    N2 = [delta * (Z^2 - M^2 Dmain) - U^2 Cy]^2
         - 4 delta M^2 Dmain U^2 Cy.

Every symbol is an explicitly defined integer polynomial, not another
quantified variable. The complete formula is in the article's Section 3
and `integer/FAMILY.md`; its division-free literal arithmetic circuit is
`integer/equations/integer16_crt_valuation_degree124.json`.

The new reduction retains selected Pell roots, recovers their equations by
an integer-unit argument, and combines the remaining roots using distinct
3-adic valuations. A coprime carrier restores both the cubic scale and the
main Pell congruence. The auxiliary root's integrality is proved by descent.
All sign and denominator conditions are recovered in the order needed.

Against the existing 16-integer degree-184/135-operation construction, the
new equation lowers degree by **32.6%** and operations by **12.6%**.

| Domain | Variables | Exact degree | Live operations |
|---|---:|---:|---:|
| Unrestricted integers | 13 | 1072 | 195 |
| Unrestricted integers | 14 | 414 | 148 |
| Unrestricted integers | 15 | 218 | 130 |
| Unrestricted integers | 16 | 124 | 118 |
| Strictly positive integers | 12 | 70 | 98 |
| Strictly positive integers | 13 | 51 | 88 |

The 13-integer form improves degree 1088/195 at unchanged cost. The
14-integer form improves the inspected degree 696/150 and 652/230 points.
The 15-integer form trades four degrees for nine operations against 214/139.
The positive companions remove an unnecessary congruence restriction on J.

Operations count every live binary addition, subtraction, and multiplication,
including squares and fixed scalar multiplication. Input/numeral leaves and
reuse of a computed value are free under this declared convention.

## A direct alternative without K215 or Jones's universal polynomial

The direct component compiles the calibrated C222 proof-certificate calculus
using a smaller, proved Pell graph for positive exponentiation.

| Direct form | Domain | Variables | Degree | Quadratic rows | Expanded terms | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| Main quartic | Nonnegative integers | 2473 | 4 | 2089 | 20580 | 127808289 |
| Smaller coefficients | Nonnegative integers | 4860 | 4 | 4476 | 14719 | 1837 |
| Standard integer lift | Integers | 7419 | 8 | 2089 fourth-degree residuals | Not collected | Not measured |

The main direct quartic improves 3614→2473 variables, a 31.57% reduction;
its expanded monomial count increases. The second variant improves variables,
residuals, monomials, and height while retaining degree four, against its
corresponding 6183-variable/height-1993 parent.
Both quartics are supplied fully expanded with literal integer coefficients.

The new positive-power graph has **eleven auxiliary natural coordinates
and six equations** before arithmetic wires are introduced. The proof
orients four congruence quotients, fixes W=n+k without losing completeness,
and then eliminates three coordinates through nonnegative polynomial definitions.
The complete source uses this graph at 55 calls with proved positive inputs.

## Exact scope of the consistency theorem

For each equation with its stated domain D, the ordinary proof establishes

    ZFC proves: [no x in D^m with P(x)=0] iff Con(ZFC).

The new reductions are proved here. This conclusion composes them with
the explicitly retained **ordinary** calibration theorems:

- native/compiler/K215 calibration for the integer and positive families;
- C222/Horn/CRT and C222–ZF–ZFC finite-refutation calibration for the direct family.

It neither assumes nor proves consistency. It is not a new end-to-end Lean
or Rocq certificate, an exported derivation in the encoded object-language
ZFC calculus, or external peer review. The full transitive calibration
was not independently reproved in this package. Finite checks certify
literal algebra and data; they do not replace the unbounded proofs.

No absolute simplicity optimum or world minimum-variable record is claimed.
Existing nine-positive and ten-integer constructions retain fewer variables
at substantially higher degree. The coefficient tuples of the two native
branches are different and must not be mixed.

## Contents and reproduction

- `report/`: comprehensive article, PDF, and complete LaTeX source.
- `integer/`: four unrestricted-integer DAGs, proofs, six exact numerals,
  finite coefficient recipe, retained upstream sources, and verifiers.
- `direct/`: two fully expanded quartics, integer lift, literal calculus,
  deterministic compiler, new power proof, and independent SOS checker.
- `positive/`: two positive-variable DAGs, free-J proof, authentic compact44
  tuple and recipe, parent equations, and checks.
- `verification/`: successful root replay receipts and visual-layout record.
- `provenance/`: root source ledger.
- `MANIFEST.json`: content hashes for the delivered package.

Python 3.10+ and SymPy 1.14 suffice (the integer and direct parts use the
standard library). Install the small declared dependency, then run:

```sh
python3 -m pip install -r requirements.txt
python3 verify.py
python3 -O verify.py
```

The root verifier uses temporary copies and leaves sealed files unchanged.
For an external receipt, add `--output /absolute/path/outside/package.json`.
Individual component commands are documented within each component.

Rebuild the PDF with ordinary pdfLaTeX:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Incorporation

Place this directory beside the existing proposals under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms`, selecting
its numeric prefix at incorporation time. No repository file is overwritten
and no formal endpoint is replaced by this delivery. Original licenses
and notices accompany inherited material. New text and code follow the
repository's MIT No Attribution license.

