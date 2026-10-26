# A diagonal growth certificate for Diophantine consistency of ZFC

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.
Mathematical development, implementation, and independent internal review
were assisted by ChatGPT.

## The equation and its theorem

This package supplies the explicit polynomial

\[
Q_{214}(x_0,\ldots,x_{213})
=\sum_{j=0}^{152}R_j(x_0,\ldots,x_{213})^2,
\qquad (x_0,\ldots,x_{213})\in\mathbb Z^{214}.
\]

Each of the 153 residuals is a literal polynomial of degree at most two.
The complete list appears in the report, in `residuals.tex`, and in
`direct/diagonal214/residuals.txt`. The machine-readable definition is
`direct/diagonal214/equation.json`; its fully collected quartic expansion
is `direct/diagonal214/expanded_polynomial.json`.

The ordinary mathematical proof, composed with the explicitly identified
inherited Pell and C222 logical calibrations, establishes

\[
\mathrm{ZFC}\vdash
\left(\neg\exists\boldsymbol x\in\mathbb Z^{214}\;
Q_{214}(\boldsymbol x)=0\right)
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

Here consistency is the absence of a finite refutation in the fixed
effective ZFC presentation identified in `SOURCES.md` and the dependency
note. The equivalence is proved uniformly for the internally coded
integers and finite derivations of ZFC. It uses no assumption that ZFC is
consistent and proves neither consistency nor inconsistency.

All 214 unknowns range independently over unrestricted integers. Every
coefficient is explicitly supplied. The final polynomial uses only
addition and multiplication with integer constants and fixed exponents;
the variable powers discussed in the semantic proof are represented by
the retained ordinary polynomial Pell equations.

## Measured result and comparison

| Equation | Integer variables | Quadratic residuals | Exact degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Source 173 principal P215 | 215 | 154 | 4 | 5,660 | 91,679 |
| Source 173 companion P214 | 214 | 153 | 4 | 5,486 | 1,099,511,627,852 |
| **This package: Q214** | **214** | **153** | **4** | **5,656** | **219,813** |

Height means the largest absolute coefficient after collecting the
expanded polynomial. The new residual list contains 1,040 monomials
before squaring, and its largest absolute coefficient is 464.

Relative to the principal P215, Q214 removes one unknown and one residual,
reduces the expanded support by four monomials, and increases coefficient
height. Relative to the existing P214 companion, it retains the same
dimension and degree, lowers coefficient height by a factor exceeding
five million, and adds 170 collected monomials. These are specific
tradeoffs. Source 173 also supplies a 213-variable companion with much
larger coefficients; this package does not claim a new minimum variable
count or a globally simplest equation.

The exact parent is pinned at commit
`02a78a08603cbae248c19c23a75907c6c6bd6443`. Its original equation bytes
are retained under `direct/principal/`; the source paths and hashes are
listed in `SOURCES.md`.

## What changes, and what is inherited

The new construction sets

\[
t=464+z^2,\qquad K=464t^2,\qquad F=K^K.
\]

The same existing principal Pell pair certifies index K. Using K also
as the power base replaces the parent's two index-building equations
`T2=t^2`, `K=T2^2` by the single quadratic equation `K=464*t^2`.
The private coordinate T2 disappears. Exactly five parent residuals
change, one residual is deleted, and every other retained residual is
copied literally. The square frame is updated to contain the actual new
base as well as the index; this update is essential to the proof.

A source-specific positive-polynomial bound justifies the smaller index.
For the actual C222 label polynomial J, the authenticated source DAG has
degree 524,288. Exact integer bounds at 464 and nonnegativity of all
coefficients prove, uniformly for the local parameters below t,

\[
J<t^{645888},\qquad
K^K\ge t^{645888t}.
\]

This supplies the growth required by the inherited finite-product
separation theorem. The selected t may be odd or even; K is always
even, and the proof explicitly verifies the factorial valuation and
odd-binomial conditions in both cases.

The self-power idea already occurs in source 170. Removal of the
derived-label range, the sharp product-separation lemma, and reuse of the
CRT row-index representative C as a cofinal Pell anchor belong to source
173. The present contribution is the verified composition at that
interface, the sharper source-bound certificate, and the fully emitted
214-variable quartic with the measured coefficient tradeoff. No claim of
worldwide priority is made.

## Files

| Path | Contents |
|---|---|
| `report.tex`, `report.pdf` | Complete article, proof, comparison, and literal residual appendix |
| `residuals.tex` | Generated TeX for every one of the 153 residuals |
| `direct/diagonal214/` | Final equation, full expansion, residual text, variable chart, metrics, and exact source-change certificate |
| `direct/principal/` | Preserved source 173 principal equation used as the authenticated parent |
| `direct/DIAGONAL_PROOF.md` | Detailed new soundness, completeness, growth, parity, and interface argument |
| `direct/build_diagonal.py` | Deterministic producer from the authenticated parent equation |
| `majorant/` | Exact square-shell source, standalone majorant checker, finite certificate, and uniform growth proof |
| `inherited/parent173/` | Selected retained source 173 proof and calibration notes |
| `inherited/PRIOR_DIAGONAL_SOURCE_PROOF.md` | Earlier self-power construction from source 170, preserved for attribution and comparison |
| `inherited/logical/` | Selected pinned logical endpoint source files and their source ledger; no complete Lean import closure |
| `verification/` | Finite verification receipts and an independent review of the new transformation |
| `verify.py` | Independent coefficient, source-change, printed-formula, majorant, and rebuild checks |
| `evaluate.py` | Exact evaluation at a supplied JSON list of 214 integers; it does not search for roots |
| `code/export_report.py` | Regeneration and validation of the printed residual appendix |
| `SOURCES.md`, `LICENSE` | Source identities, attribution, dependency boundary, and reuse terms |

## Verify and rebuild

Extract the ZIP and run these commands from the extracted package directory.
Python 3.10 or later and its standard library suffice for the mathematical
artifact checks. They need no network access.

```bash
python3 -B verify.py --rebuild
python3 -B -O verify.py --rebuild --exact-majorant
```

The first command reconstructs the final equation from the preserved
parent in a temporary directory and compares all emitted files. Both
commands recollect every quartic coefficient independently, check all
retained and changed residuals, verify the actual frame/index bindings,
check variable occurrence and exact metrics, validate all printed
residuals, and reject deliberate corruptions of the five changed rows.

The second command additionally cross-checks the majorant with complete
huge-integer evaluation. The normal majorant check already uses exact
integer dyadic intervals; neither mode uses floating-point estimates.
The `-O` run verifies that substantive checks remain active when Python
assertions are disabled. Both commands print a JSON receipt. For a
separate saved receipt, append `--receipt /tmp/conzfc-diagonal-replay.json`.

To evaluate the polynomial at a chosen tuple, put exactly 214 integers
in a JSON list and run:

```bash
python3 -B evaluate.py tuple.json --residuals
```

The optional `--modulus` argument computes a modular diagnostic; a
modular zero is not evidence of an integer zero.

To rebuild the PDF with a standard LaTeX installation, run twice from
the package directory:

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

TeX versions, timestamps, or font metadata can change PDF bytes without
changing the mathematical content. The polynomial and finite-check
artifacts are reproducible independently of the PDF toolchain.

## Proof and verification boundary

The ordinary proof establishes the unbounded arithmetic interpretation
and composes it with the explicitly credited C222/ZF/ZFC calibration.
Finite checks establish the literal equation, exact algebraic edits,
coefficient collection, source-bound constants, and reproducibility.
They do not prove the inherited Pell or logical theorems by sampling.

This release supplies no new complete Lean/Rocq verification or encoded
object-language ZFC derivation. The selected logical source files are
retained for precise attribution and inspection; their full dependency
closure was not rebuilt here. The mathematical review was internal and
AI-assisted, and is not represented as external human peer review.

For repository integration, preserve this package as a new named directory
under `Computability/DiophantineConsistency/con-zfc-diophantine-forms/`,
alongside the existing tradeoffs. The integration process may assign an
intake number. Keep the parent equation and source ledgers with the new
equation so its exact change and calibration remain reviewable.
