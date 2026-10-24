# Smaller direct quartic equations for ZFC consistency

## Recommended result

The recommended equation is a fully specified polynomial of **exact degree 4 in 3,776 unrestricted integer variables**, with **20,194 nonzero monomials** and **maximum absolute coefficient 47,959**.

On the named established C222-calculus and finite arithmetic representation theorems, the article gives an ordinary mathematical proof in ZFC of

\[
\neg\exists\boldsymbol x\in\mathbb Z^{3776}\,P(\boldsymbol x)=0
\quad\longleftrightarrow\quad\operatorname{Con}(\mathrm{ZFC}).
\]

This direct construction does not encode K215 and does not use Jones's universal polynomial. It builds on the repository's direct C222 proof-calculus equation, then proves new exact algebraic reductions. It is a substantial improvement within that direct quartic family, not a global minimum-variable or simplicity claim.

| Equation | Integer variables | Quadratic residuals | Degree | Nonzero monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Repository baseline | 8,619 | 4,619 | 4 | 39,811 | 127,285,349 |
| **Recommended** | **3,776** | **2,015** | **4** | **20,194** | **47,959** |
| Fewer-variable companion | 3,671 | 1,942 | 4 | 26,271 | 3,835,369,234 |
| Smallest-coefficient retained companion | 7,058 | 5,297 | 4 | 24,277 | 1,992 |

Against the baseline, the recommended polynomial saves 4,843 variables (56.19%) and 19,617 monomials (49.28%). Its coefficient height is about 2,654 times smaller. The 3,671-variable equation saves 105 additional variables but has substantially larger coefficients. The full intermediate constructions are retained to make the proof chain reproducible.

## Start here

- `report/report.pdf`: the comprehensive article, including all new proofs, source-calibration discussion, comparisons, and further research questions.
- `report/report.tex`, `report/metrics.tex`: editable LaTeX sources.
- `equations/main/equation.json`: all 2,015 quadratic residuals for the recommended equation.
- `equations/main/expanded_polynomial.json`: the entire collected polynomial, with no free parameters or remaining arithmetic macros.
- `equations/main/residuals.txt`: an ordinary text rendering of all residuals.
- `equations/main/elimination_certificate.json`: the complete polynomial reconstruction maps.
- `equations/fewer_variables/`: the corresponding 3,671-variable endpoint.
- `guard_minimization/retained_candidate/`: the coefficient-height-1,992 equation.

Every coordinate in the final equations ranges over **all integers**. In a term `[c,[i,j]]`, the value is `c*x_i*x_j`; an empty monomial list denotes a constant. The equation is the sum of the squares of the residuals equal to zero. The expanded table is independently checked against that definition.

Recommended expanded-polynomial SHA-256:

```text
28e218143296c666cd387ef4d9ccc5a4ab0d45506a59ef2fb946c37291a17337
```

## New transformations

1. Replace 221 private differences of natural congruence quotients by genuine integer quotients, with an explicit positive/negative-part restoration.
2. Normalize 110 semantic signs by exact diagonal symmetries of every core residual.
3. Prove the remaining necessary signs by ordered polynomial implications, retaining only 645 guards in the affine source or 661 in the retained-wire source.
4. Eliminate monic coordinates by substitutions that preserve quadratic residual degree, with a unique polynomial reverse lift.

The recommended retained-wire path removes 3,282 coordinates in its final elimination pass: 1,915 affine and 1,367 quadratic substitutions. The other endpoint removes 1,208 coordinates from the affine-source intermediate.

## Offline verification

Python 3.11+ and its standard library suffice. No network access, package installation, Lean installation, or original incoming ZIP is required.

```sh
python3 verify.py
python3 -O verify.py
```

The driver works from any current directory and executes checks in a fresh temporary copy. It authenticates the release, regenerates the complete frozen natural source and the signed/guarded intermediate equations, runs the original independent arithmetic/calculus audits, independently replays every final elimination, and compares the complete expanded polynomials. It also checks adversarial certificate mutations. It does not search for a zero of the consistency polynomial.

To rerun the slower elimination optimization as well:

```sh
python3 verify.py --regenerate
```

To create a fresh receipt, add `--receipt /absolute/path/receipt.json`. No delivered file is rewritten by default. The recorded release runs are in `verification/`.

The new independent checkers do not import their optimizers. Their failure checks remain active with `python -O`. Universal mathematical proofs establish why their certificate rules preserve zero existence; exact replay establishes that the delivered coefficient tables instantiate those rules.

## Rebuild the PDF

With TeX Live or MiKTeX:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Provenance and proof status

The comparison snapshot is ProveIt commit `278bc68df1af125d62f9cbfe28c9fd3ebcf50d5b`. The exact natural parent, seven original arithmetic/audit files, licenses, proof notes, and selected pinned calibration interfaces are included. `source_calibration/SOURCE_URLS.json` records the exact repository paths, revisions, SHA-256 hashes, Git blob identities, and byte lengths of the read-only Lean excerpts. They are not a complete buildable Lean checkout.

The claim is an ordinary mathematical theorem of ZFC using explicitly named proved dependencies. No new end-to-end Lean theorem, freshly rebuilt upstream Lean closure, or emitted object-language ZFC derivation is claimed. No consistency assumption is used to prove the biconditional. The package proves neither consistency nor inconsistency of ZFC.

The repository already has equations with fewer variables and higher degree, including nine-natural-variable and ten-integer-variable constructions. The improvement here concerns the direct, moderate-coefficient quartic family. Global optimality and historical novelty of the underlying general algebraic ideas are not asserted.

The package can be incorporated into a new candidate directory or placed in `docs/incoming`. Existing repository files need not be overwritten.
