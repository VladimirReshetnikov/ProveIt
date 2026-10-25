# Symmetric residue budgets for Diophantine consistency

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Start with **ConZFC_Symmetric_Residue_Budgets.pdf**, the 20-page research paper.
Its editable source is `report/main.tex`. The paper prints every one of the
principal equation's 186 quadratic residuals and the complete compact formulas
and fixed coefficient recipe.

## Main equation

All 258 coordinates are unrestricted integers. Define

    P258(x0,...,x257) = sum(r_j(x)^2 for j=0,...,185) = 0.

Every residual is supplied in `equations/P258/equation.json`, printed in the
paper and `residuals.tex`, and expanded in `expanded_polynomial.json`.
There is no variable exponent, factorial, binomial, undecided coefficient,
or external predicate in the actual polynomial.

The ordinary mathematical proof, composed with the retained named
C222/ZF/ZFC refutation interfaces, gives:

> ZFC proves that P258 has no integer zero if and only if Con(ZFC).

The proof is formalizable in ZFC. This release does not supply a newly checked
end-to-end Lean/Rocq development or an encoded object-ZFC proof. It neither
proves Con(ZFC) nor asserts the absence of solutions independently.

| Direct construction over Z | Variables | Quadratic residuals | Degree | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Matched incoming parent | 282 | 192 | 4 | 5,491 | 128,446 |
| New P261 companion | 261 | 185 | 4 | 5,332 | 47,281 |
| **New P258 main** | **258** | **186** | **4** | **5,319** | **47,281** |

The comparison pin is `e0c98c629bf10d30b695884f6b1d2ab361bdf513`, including
all six incoming archives. The matched parent is the round-17 cofinal-anchor
archive's `direct/strict_dimension_centered` equation. These improvements
are within the direct numerical proof-calculus lineage. They are not a global
variable-count record or a global simplicity optimum. The direct branch uses
neither a K215 simulation nor Jones's universal polynomial.

## Main mathematical changes

1. Replace eleven private remainder interval certificates with four symmetric
   quadratic budgets. Prove a q/16 bound for each required low binomial
   coefficient **before** the factorial fixed point. The canonical residues
   then lie below D/8, while the shared budget gives absolute remainders below
   D/2. Exact congruences force equality and recover every missing sign.
2. Merge the two q^t remainders into the q^(t+1) group using only two product
   coordinates. Three shared budgets remain.
3. Replace an initial three-coordinate sign graph by the one-coordinate
   equation q=(2z+1)^2. A different bootstrap proves the old sign afterward;
   compatible CRT parity choices prove completeness.
4. Apply thirty reversible elementary residual-row operations. They preserve
   the entire zero set and lower coefficient height without changing degree,
   variable count, or the final support count.

The two compact companions in `compact/` have **ten strictly positive** integer
variables and retain their native/K215 ancestry. They save one addition each:

| Literal compact equation | Binary operations | Exact degree | Matched parent operations |
|---|---:|---:|---:|
| equation77_degree630.json | 77 | 630 | 78 |
| equation78_degree468.json | 78 | 468 | 79 |

Their new signed Pell proof shows every positive zero forces T>alpha, so
removing T+alpha from the old auxiliary shift gives an explicit bijection of
positive zero sets. These are a different domain and complexity tradeoff
from the unrestricted-integer quartics.

## Offline verification

Python 3.10 or later and its standard library suffice. No network, original
checkout, external symbolic algebra system, or proof assistant is required.

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B build_endpoints.py --check
```

The default verifier is read-only. To save a receipt, use `--receipt PATH`,
preferably outside the sealed release folder. It checks the exact source
boundary, Horn factorization identities, monic restorations, coordinate
translations, all thirty row operations forward and backward, every quartic
coefficient, every printed residual, all compact circuit cuts, all fixed
numerals, degrees, counts, and deliberate corruption controls.

The finite checks authenticate the artifact; the unbounded mathematical
arguments are in the paper, `direct/PROOF.md`, `compact/PROOF.md`, and the
retained source proofs. Independent reviews mean separately performed
reviews within this AI-assisted workflow, not outside human peer review.

For exact evaluation at an ordered JSON list of 258 integers:

```sh
python3 -B evaluate.py point.json
```

Use `--equation P261` with 261 coordinates for the companion. These are exact
evaluators, not solvers or consistency decision procedures.

To rebuild the PDF using a standard TeX Live installation:

```sh
sh build_report.sh
```

PDF bytes can change with TeX versions and metadata. Rebuilding in place may
invalidate the original PDF hash; the literal JSON equations are canonical.

## File map

- `equations/P258/`, `equations/P261/`: complete final residuals, collected
  polynomials, metrics, variable names and exact row-operation certificates.
- `direct/`: literal source, all finite construction stages, proofs and checker.
- `compact/`: both new circuits, unchanged coefficient payloads, independent
  finite reconstruction, new proof and complete retained compact parent.
- `sources/`: inherited ordinary arithmetic proofs, calibration interface
  source, original comparison equation and source metrics.
- `review/`: scoped independent mathematics/algebra reviews, complete release
  receipts, and a clearly marked uncompiled alternative proof-calculus idea.
- `research/`: the finite heuristic used to find residual transformations.
  The explicit operation certificates suffice to replay the result.
- `SOURCE_LEDGER.json`: exact repository/archive provenance.
- `MANIFEST_SHA256.json`: checksums of the sealed payload.

Sparse terms `[c,[i,j,...]]` mean `c*x_i*x_j*...`; repeated indices are repeated
factors and an empty list denotes a constant. Every sum is finite and every
coefficient is an ordinary fixed integer.

The release can be placed as a new research package after repository review.
No repository branch, pull request, issue, or upstream file was changed.
Inherited licenses and attribution notices are retained. New material follows
the repository's MIT No Attribution license.
