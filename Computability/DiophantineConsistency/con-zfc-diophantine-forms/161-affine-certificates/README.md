# Affine certificates for direct quartic Con(ZFC) equations

Prepared for Vladimir Reshetnikov, 25 October 2026.

The main result is an explicit quartic in **238 unrestricted integer
unknowns**, with **174 quadratic residuals**, **12,789 collected monomials**,
and coefficient height **7,968**. A balanced alternative uses **239 integers**,
**175 residuals**, and **5,044 monomials**, at the same degree and height.

Two further quartics use 237 and 238 variables with larger coefficients.
All equations are fully specified by finite integer-coefficient lists.

| Directory | Variables | Residuals | Degree | Monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| `equations/balanced239` | 239 | 175 | 4 | 5,044 | 7,968 |
| `equations/fewer238` | 238 | 174 | 4 | 12,789 | 7,968 |
| `equations/horizon238` | 238 | 174 | 4 | 5,042 | 1298074204962300530359575779475468 |
| `equations/horizon237` | 237 | 173 | 4 | 12,787 | 1298074204962300530359575779475468 |

For each supplied residual list `r[0], ..., r[m-1]`, the equation is

    P(X) = sum(r[j](X)^2 for j in range(m)) = 0,  X in Z^n.

The ordinary mathematical proof, composed with the repository's retained
C222-to-ZFC refutation calibration, establishes in ZFC:

    (P has no integer zero) <=> Con(ZFC).

This is not a proof of consistency, a global simplicity minimum, or a new
end-to-end Lean/Rocq or object-language ZFC formalization. The encoding is
directly through C222 derivations; no K215 computation or Jones universal
polynomial is compiled into these new equations.

## What is new

1. In the factorial-free source, replace `q=(2z+1)^2` by `q=4z+1`.
   Signed power certificates exclude exceptional bases; centered signed
   binomial digits recover a positive binomial and then a positive radix.
2. Replace the beta scale `y=F(2v+1)^2` by `y=F(2v+1)`.
   Its sign is recovered from the retained power request at exponent `y+1`.
   Two now-affine coordinates and rows are removed.
3. Eliminate the Pell discriminant `D=a^2+2a` modulo a retained product
   relation `Z=(a+1)Y`. The identity
   `aZ-(a^2+2a)Y-a(Z-aY-Y)=-aY` preserves quadratic residual degree.
   The additional linear occurrence of D in the last norm is substituted too.
4. In the larger-coefficient alternative, replace the growth base by
   `d=2^26(2t+1)`. Its existing signed power request forces `t>=0`;
   endpoint parity excludes `t=0`. The separate horizon-square row and
   its private witness can be deleted.

The first three steps remove three unknowns and three rows from each
immediate factorial-free parent at unchanged degree and coefficient height.
The fourth step removes one more unknown and row, with a substantial height
tradeoff. The balanced 239-variable form is the recommended readable
small-coefficient integration target; the 238-variable form is supplied
when fewer quantified integers matter more than expanded support.

## Contents

- `report/manuscript.tex` and `report/manuscript.pdf`: complete article,
  proofs, comparisons, limitations, further questions, and all 175 quadratic
  residuals of the balanced form printed in an appendix.
- `report/residuals239.tex`: mechanically generated complete residual appendix.
- `equations/`: four complete final systems, collected polynomials, exact
  metrics, source equations, coordinate-restoration certificates, and checks.
- `stages/`: retained affine and horizon source stages and full certificates.
- `proofs/`: detailed unbounded proofs and independent mathematical review.
- `tools/`: standard-library constructors, independent verifiers, evaluator,
  reproduction wrapper, and appendix generator.
- `verification/`: actual finite audit and full reproduction receipts.
- `provenance/`: unmodified incoming parent archive and exact source ledger.
- `MANIFEST.sha256`: integrity hashes of all delivered members except itself.

## Reproduction

Run from this directory:

```sh
python3 tools/reproduce.py
python3 -O tools/reproduce.py
```

The wrapper rebuilds in a temporary directory and compares all final data
with the delivered artifacts. It never imports code from the inherited ZIP
and needs no network connection or third-party Python package. It verifies
the full source lineage, 202 inherited monic eliminations, every changed
row, all restoration maps, all collected coefficients, exact degree and
height, all-coordinate liveness, and mutation-rejection controls. The
separate ordinary proofs establish the unbounded arithmetic claims.

To regenerate and compile the PDF:

```sh
python3 tools/build_report.py
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=report report/manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=report report/manuscript.tex
```

The TeX source uses standard packages including `amsmath`, `amsthm`,
`lmodern`, `microtype`, `hyperref`, and `xurl`. PDF byte identity can depend
on the installed TeX version; equation JSON and source hashes are the
mathematical identifiers.

## Exact baseline and proof scope

Repository: https://github.com/VladimirReshetnikov/ProveIt

Revision: `f7ed4a58c38c2f8d897917f68e5b8eb04609bf87`

Source path:
`docs/incoming/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip`

SHA-256:
`38dfec4f7db8ba4af921fe101714da6a569a3afce1d916325eb550160372c913`

The unchanged signed Pell orientation, generalized binomial CRT,
local C222 rule checker, and C222/refutation calibration are named
dependencies. The report proves the changed sign, range, horizon, and
algebraic steps and explains their composition with those dependencies.
The independent finite checks certify the literal equations, not the
consistency or inconsistency of ZFC. No proof-assistant project was rebuilt.

This package was produced with AI assistance and separate mathematical
and algebraic reviews. No literature-wide priority claim is made.
