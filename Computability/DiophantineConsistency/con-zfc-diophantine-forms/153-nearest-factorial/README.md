# Nearest-factorial certificates for Diophantine consistency

Research prepared with AI assistance for Vladimir Reshetnikov and ProveIt,
25 October 2026.

Start with **`report/report.pdf`**. Its editable source is
**`report/report.tex`**, with generated metric and residual appendices beside
it. The article prints all 178 residuals of the principal quartic. This
package also contains complete equations, fixed coefficient data, ordinary
proofs, exact inverse certificates, deterministic reconstruction code, and
separately implemented finite checkers.

For each supplied polynomial P, with its explicitly stated domain D and
number n of unknowns, the theorem is:

    ZFC proves:
    [there is no x in D^n with P(x)=0] if and only if Con(ZFC).

Here Con(ZFC) means that no finite syntactic ZFC refutation exists. The theorem
does not establish the truth of either side separately.

## Main result: direct quartics over all integers

The principal equations use the numerical C222 proof calculus directly.
Their construction does not simulate K215 or instantiate Jones's universal
polynomial. Each is exactly the sum of the squares of the residuals listed
in its `equation.json`; its adjacent `expanded_polynomial.json` supplies
every collected integer coefficient.

| Construction | Integer variables | Quadratic residuals | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Matched incoming common-remainder parent | 252 | 182 | 4 | 5,340 | 128,446 |
| New arithmetic stage, before the final row reductions | 246 | 182 | 4 | 6,576 | 412,187 |
| **`direct/equations/P242`** | **242** | **178** | **4** | **17,026** | **38,432** |
| **`direct/equations/P243`** | **243** | **179** | **4** | **6,877** | **11,856** |

P242 saves ten variables and four residuals against the matched 252-variable
parent, and lowers its coefficient height. Its expansion is larger. P243
saves nine variables and three residuals, and offers substantially smaller
support and height than P242. Neither final polynomial dominates the matched
parent in every measure, because both increase support. There is no claim
that either is globally simplest or has the fewest possible unknowns.

The new arithmetic idea is a **signed nearest-integer factorial certificate**.
For integers t >= 16 and F >= 1,

    |F - (F^2+1)^t / binom(F^2+t,t)| < 1/2   iff   F=t!.

The error at F=t! is positive and less than 1/32. This lets a single common
residue budget absorb the factorial ceiling. The proof first excludes a
degenerate radix, then obtains x >= t+1 from an existing divisibility
constraint, excludes F=0 and negative branches, and only then recovers the
factorial and the missing signs. Both old ceiling nonnegativity guards are
removed. The credited odd-square radix construction replaces the third
front guard. Four previously identified affine consequences are transferred
and checked exactly to reach the final dimensions.

The displayed powers, factorial, and binomial in this explanation describe
the proof. **They are not operations in the final ordinary quartics.** The
literal residual lists use integer coefficients, addition, subtraction,
and multiplication only.

## Further exact tradeoffs over unrestricted integers

The `signed/` component supplies four additional fixed ordinary polynomials.
It retains a different, native/compiler/refutation ancestry with fully bound
large integer coefficients. Intermediate circuit registers are polynomial
abbreviations; the ordered `variables` list alone declares the unknowns.

| Complete circuit | Unknowns over Z | Exact degree | Binary operations | Matched parent's degree / operations |
|---|---:|---:|---:|---:|
| `signed/integer14_degree82.json` | 14 | 82 | 113 | 86 / 112 |
| `signed/integer14_degree90.json` | 14 | 90 | 111 | 94 / 110 |
| `signed/integer13_degree152.json` | 13 | 152 | 126 | 156 / 125 |
| `signed/integer11_degree298.json` | 11 | 298 | 150 | 300 / 148 |

These lower degree at a small additional operation cost. They do not improve
both columns at once. The new first-index argument uses an already available
Pell modulus XY^2 to reduce a magnitude budget from q^8 to q^6; the
11-variable polynomial adds an integral center term that takes advantage
of the lower budget degree. `signed/PROOF.md` supplies the unbounded proof,
and all six fixed coefficients have complete byte payloads and a finite
reconstruction. Collected support and coefficient height for these larger
scalar polynomials are not measured in this release.

## A shorter evaluator for an existing ten-positive-variable polynomial

`compact/equation79_degree382.json` evaluates a polynomial in **ten strictly
positive integers**, of exact degree **382**, using **79 binary operations**.
Its matched incoming evaluator used 80 operations. The polynomial itself,
its coefficient tuple, and its positive zero set are unchanged: the one-gate
saving follows from sharing the product kY and the identity

    (D*Y)*k = D*(k*Y).

This is a circuit improvement, not a new polynomial or a variable-count
improvement. The positive domain is part of the theorem; it must not be
silently replaced by all integers or by the nonnegative integers. This
component retains its inherited native/K215 calibration. Its four fixed
coefficient ports are supplied and are not additional unknowns.

For all circuit counts, binary addition, subtraction, and multiplication
count as operations, including squaring and multiplication by a fixed
scalar. These counts do not assert bit complexity or a global circuit
lower bound. `RESULTS.json` records the exact domains, metrics, and paths.

## Verify and rebuild offline

From the package root, with Python 3.10 or later and its standard library:

```sh
python3 -B verify.py
python3 -B verify.py --rebuild
python3 -B -O verify.py --rebuild
```

The verifier checks the supplied mathematical objects, source bindings,
exact algebraic transformations, coefficient data, and component mutation
controls. The rebuild mode replays the supported deterministic mathematical
reconstructions and compares their outputs with the supplied artifacts.
The final direct-polynomial replay uses frozen finite certificates rather
than rerunning the optimizer. Component READMEs document their individual
commands and the precise scope of each check.

With a normal pdfLaTeX installation:

```sh
python3 -B build_report.py
```

This checks the article's generated inputs against the authoritative equation
data and builds `report/report.pdf`. Mathematical JSON and coefficient payloads
are the reproducibility targets. PDF metadata, font bytes, and line breaking
can vary with the TeX installation, so cross-installation PDF byte identity
is not required. No arithmetic verifier requires network access, a parent
repository checkout, or a search for a refutation.

The release manifest binds the supplied source and data. The generated PDF
and the two top-level run receipts are excluded so that the PDF can be
rebuilt with another TeX installation and verification can be rerun. The
released PDF hash is recorded in `review/pdf_build.json`; the archive hash
binds the complete delivered package.

## What is proved and what is checked

The new arithmetic lemmas and their soundness/completeness directions are
ordinary mathematical proofs formalizable in ZFC. Their consistency
interpretation composes them with the explicitly retained logical calibration
of the appropriate predecessor construction. The direct chain uses the named
C222/ZF and ZF/ZFC refutation interfaces; the other components identify their
native/compiler/refutation dependencies separately.

The finite checkers certify the literal polynomials, fixed coefficients,
exact transformations, and recorded metrics. They do not replace the
unbounded Pell, CRT, factorial, or logical arguments. This release supplies
**no newly compiled end-to-end Lean/Rocq proof or encoded object-ZFC proof
term** for the new endpoint. Retained formal-interface source files are
identified dependencies; their inclusion is not a claim that every transitive
formal dependency was rebuilt. The scoped review files make this boundary
explicit.

## Provenance and layout

The comparison snapshot is:

    VladimirReshetnikov/ProveIt
    3ecd6a6cf53d47519228328567f45fb7ee9781d9

The eight incoming archives at that snapshot were inventoried and their
stated endpoints inspected. This is not an assertion that every previous
package was independently rebuilt. Exact immediate-source and archive
identities are preserved in the component provenance ledgers.

- `report/`: article source, generated appendix, and PDF.
- `direct/`: P242/P243, nearest-factorial proof, complete residual expansions,
  transformation certificates, checkers, and retained proof dependencies.
- `signed/`: four smaller-variable scalar equations, fixed coefficient
  reconstruction, proofs, and exact gate/degree checks.
- `compact/`: the identical degree-382 polynomial with a shorter evaluator.
- `review/`: scoped mathematical and internalization reviews.
- `RESULTS.json`: exact result inventory and comparison metrics.
- `INTEGRATION.md`: suggested repository intake and review procedure.
- `NOTICE.md`: attribution and the relationship to retained source notices.

No literature-wide priority, global simplicity optimum, proof of consistency,
or outside human peer review is claimed. The main achieved result is the new
nearest-factorial arithmetic reduction and its fully explicit direct quartics.
