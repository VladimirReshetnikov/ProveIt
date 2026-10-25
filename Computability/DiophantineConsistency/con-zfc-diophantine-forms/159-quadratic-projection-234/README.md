# A direct quartic for Con(ZFC) in 234 integer variables

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.
Repository comparison snapshot: `7a8da414376a80b90ecf799f37ceb26fb9ac674e`.

## Main result

The principal literal polynomial is `equations/P234/equation.json`:

P234(x0,...,x233) = sum(Q_i(x)^2, i=0,...,170).

Every variable ranges over the unrestricted integers. Every Q_i is an explicitly
listed quadratic with integer coefficients. The complete expanded polynomial is
also supplied. Composing the proved integer zero-set bijection with the pinned
parent calibration gives, in ZFC, no integer zero if and only if Con(ZFC).

| Equation | Integer variables | Quadratic residuals | Degree | Collected monomials | Maximum absolute coefficient |
|---|---:|---:|---:|---:|---:|
| Shared-error parent | 240 | 177 | 4 | 21,482 | 6,144 |
| **P234, principal** | **234** | **171** | **4** | **19,050** | **4,480** |
| P235_beta, factorial-free | 235 | 170 | 4 | 18,550 | 4,576 |
| P236_beta, smaller support | 236 | 171 | 4 | 4,947 | 16,866 |

The principal equation improves all four listed size measures over its actual
240-variable parent, with degree unchanged. The factorial-free companions have
a different arithmetic source; their smaller number of residuals or monomials
is a separate tradeoff.

This is a reduction in the direct small-coefficient C222 branch. The repository
already contains equations with fewer variables on other branches. No global
simplicity minimum, literature-wide priority, proof of Con(ZFC), or completed
end-to-end Lean/Rocq formalization is claimed.

## What changed

1. Six common directions of the quadratic parts let us remove six variables by
   explicit integral polynomial maps. The new independent checker reconstructs
   the result by a different exact identity from the discovery code.
2. Reversible integer row operations reduce coefficient height and support.
3. In the factorial-free branch, replace `m=(2w+1)^2, y=Fm` by
   `y=F^2+u^2+v^2`. An elementary prime-power/CRT proof supplies arbitrarily large
   multiples of t! in this family. This removes one residual and an exceptional
   soundness case. It is an existential arithmetic change, not a coordinate map.
4. A further unit affine equation gives the 235-variable companion.

The report prints every principal residual and proves the new steps. Both
unchanged source archives, their licenses, and their ordinary proof closures
are retained in `sources/`. The new equations can be evaluated without opening
or executing either source archive.

## Verification

Requires Python 3.10 or later and only its standard library:

```sh
python3 -B verify.py
python3 -B -O verify.py
```

To save a fresh detailed receipt without altering the sealed package:

```sh
python3 -B verify.py --receipt /tmp/conzfc234-verification.json
```

The verifier checks archive hashes and exact parent members, literal source
edits, every projection identity, inverse integer row operations, all expanded
coefficients, exact metrics, limited rank certificates, the printed principal
equation, and deliberate corrupted-certificate controls. It does not search
for a zero. The 195 cofinal-spacing examples illustrate an unbounded theorem;
they are not its proof.

The source parent's original release checker was also replayed successfully.
Its detailed receipt is retained in `verification/`. The complete transitive
Lean/Rocq developments were not rebuilt. The ordinary logical dependencies are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

## Reading and reproducibility

- `report/report.pdf` and `report/report.tex`: main article and LaTeX source.
- `report/residuals234.tex`: every principal quadratic residual.
- `equations/`: final literal residual lists, complete expanded coefficients,
  exact metrics, and reversible row certificates.
- `stages/`: pinned parent equations and the exact intermediate systems needed
  to replay the projection certificates.
- `code/audit_projection.py`: independent standard-library certificate checker.
- `code/reduce_radical.py`, `code/reduce_basis.py`: discovery/construction tools.
- `code/affine_search.py`, `code/affine_project.py`: exact affine consequence tools.
- `code/beta_two_squares.py`: arithmetic-source constructor and sample witnesses.
- `code/evaluate.py`: evaluates a chosen polynomial at a supplied integer tuple.
- `proofs/`: detailed projection, parent-arithmetic and beta-spacing reviews.
- `SOURCES.json`: immutable provenance; raw and canonical hashes are distinguished.
- `MANIFEST.sha256`: integrity hashes of all packaged files except itself.

The frozen certificates reconstruct the equations without rerunning a search.
The discovery scripts are also supplied for experiments; changing a heuristic
may yield a different zero-set-equivalent polynomial.

To rebuild the article (a TeX installation with the standard listed packages is
required):

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

PDF bytes can vary between TeX installations. Mathematical definitions are the
coefficient JSON and printed residuals, not the PDF metadata.

## Integration

This is an additive research submission suitable for `docs/incoming`, followed
by placement under `Computability/DiophantineConsistency/con-zfc-diophantine-forms`.
No existing repository files were changed. The two archived source submissions
are retained byte-for-byte for reproducibility and may be deduplicated at intake
using their hashes and pinned repository locations.

New material is AI-assisted research. Inherited results and limitations are
identified explicitly in the article. Source licenses remain in the unchanged
archives; the package uses the repository's MIT No Attribution license.
