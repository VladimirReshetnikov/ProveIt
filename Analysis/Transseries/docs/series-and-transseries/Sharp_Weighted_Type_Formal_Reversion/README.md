# Sharp Weighted Type Under Formal Reversion

**Zero-loss inversion, exact Borel radii, and non-D-finiteness in countable exponential feedback**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Main theorem

Let M be a positive log-convex coefficient weight, M[0] = 1. The following
are equivalent:

- M[n]^(1/n) tends to infinity.
- Every tangent-to-identity formal power series has exactly the same
  weighted coefficient limsup type as its compositional inverse.
- The inverse of every tangent-to-identity polynomial has weighted type zero.

For a general nonzero linear coefficient a, the inverse type is the forward
type divided by |a|. The proof supplies an explicit finite coefficient
majorant, with overhead exp(O(n/sqrt(M[n]^(1/n)))). Analytic pre- and
postcomposition satisfy an exact coordinate-scaling law.

The result covers all positive Gevrey weights, logarithmically refined
Gevrey weights, and log-convex superexponential weights without a
moderate-growth assumption.

## Feedback consequences

For U(q) = sum_{j>=1} q^j exp(lambda_j U(q)), lambda_j >= 0, and Q = U^(-1),
the article obtains the exact inverse Gevrey type from the existing forward
classification. It resolves the predecessor README's explicit limitation
that reversion had transferred class membership, not the sharp numerical type.

The ordinary integrated Borel transform of Q has exact radius

    1 / (4 limsup_j lambda_j / (j log j)^2).

For lambda_j = j^2, the inverse satisfies

    limsup_n ( |Q_n| log(n+e)^(2n) / n! )^(1/n) = 4.

Its Borel transform is entire, with

    limsup_r log log max_{|z|=r} |B Q(z)| / sqrt(r) = 2.

Both U and Q are non-D-finite. A more general integer-order family is
treated, and the obstruction persists under invertible analytic input
and output coordinate changes.

## Mathematical and novelty status

The abstract weight, reversion, and coordinate theorems have independent
conventional proofs in the article. Feedback applications explicitly use
two forward theorems from the repository's
`Exponential_Feedback_Regularity_Classification/article.tex`: its exact
forward Gevrey type and its regularly varying forward coefficient asymptotic.
Those are imported research results, not newly proved or independently
fully re-audited here. All new deductions are proved after stating the inputs.

No theorem in this package is claimed Lean-verified or peer-reviewed.
The source review is targeted, not an exhaustive audit of the canonical
volume or the literature. Global publication priority and a solution of a
named longstanding conjecture are not claimed. Lagrange inversion and the
basic holonomic machinery are classical.

The inverse refined coefficient statement and inverse maximum-modulus
statement are limsups, not claims of full limits or sign patterns. The
article does not prove angular Borel summability, singularity locations,
matching lower bounds on actual truncation errors, or differential
transcendence. It proposes eleven further research and formalization topics.

## Files

- `article.tex`: standalone LaTeX source with embedded bibliography and table.
- `article.pdf`: compiled A4 research article.
- `code/verify.py`: exact coefficient and finite-inequality verification.
- `data/quadratic_coefficients.csv`: exact forward and inverse coefficients.
- `data/coefficient_table.tex`: generated version of the table embedded in the source.
- `data/type_diagnostics.csv`: explicitly non-certified floating-point diagnostics.
- `data/verification.json`: recorded exact-check results and their scope.
- `data/build_validation.json`: actual PDF build and layout checks.
- `PROVENANCE.json`: pinned repository snapshot, source links, and dependency boundaries.
- `Makefile`: reproducible check and PDF build commands.

## Reproduce

The verification script requires Python 3.10 or later and no third-party
packages. The PDF requires a TeX installation with the standard packages
listed in the preamble. The TeX source compiles independently of the data
files, since the exact table is embedded.

```sh
python code/verify.py --order 70
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or run `make check` and `make pdf`.

## Recorded verification

Exact quadratic coefficients were computed through degree 70. Both inverse
compositions, the literal inverse feedback kernel, linear rescaling, the
Catalan endpoint counterexample, and one analytic composition factorization
were checked through degree 30. Twelve seeded signed-series cases passed
180 finite-majorant inequalities. Four weights passed 8,188 concentration
inequalities and the finite geometric-mean checks.

These are finite checks, not proofs of limiting assertions. The degree-70
refined-root diagnostics are about 7.59947 (forward) and 6.75803 (inverse),
not close to the asymptotic invariant 4; the article explicitly records this
preasymptotic behavior and does not use it to infer the limit.

Neither the script nor this package accesses the network or modifies
upstream repository files.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 48 (see `docs/incoming/README.md`). The
following changes were made on 2026-09-29; everything else is as delivered.

- `article.tex`: three visible "Editorial note (ProveIt, 2026-09-29)"
  paragraphs (an unnumbered environment, so the article's own numbering is
  unchanged), each preceded by a `% ed. (2026-09-29)` comment.
  At the end of Section 1.4: the gap closed here is also the regularity
  article's own research question "Exact type under compositional
  inversion" (`../Exponential_Feedback_Regularity_Classification/article.tex`,
  lines 1544-1549), cited here only through its README; the uncited
  finite-core package `../Finite_Core_Universality_Exponential_Feedback/`
  (filed in batch 47, before this article's snapshot) already implies the
  inverse type of `thm:refinedfeedback` for `lambda_j = a j^p`, `p > 2`;
  and "sharp" and "exact" refer to limsup types, radii and
  maximum-modulus limsups. After Theorem `thm:borelgrowth`: its forward
  half at `beta = 0` is the regularity article's `thm:borelintro`
  (lines 301-316), with the same constant; for `lambda_j = a j^2` the two
  batch-49 packages claim limits for the inverse. At the research question
  "Full inverse asymptotics for quadratic feedback": it re-poses the
  finite-core package's `conj:quadratic-inverse`, which this article
  neither proves nor contradicts, and for which
  `../Quadratic_Exponential_Feedback_After_Reversion/` and
  `../Signed_Quadratic_Feedback_Inversion/` (batch 49) each claim a proof,
  unreviewed. Three bibliography entries `ed:fcu`, `ed:qef`, `ed:sqf` were
  added and the widest bibliography label widened from `9` to `99`. The
  title page no longer creates a PDF page anchor (`pageanchor=false` around
  it), which removes the delivered build's duplicate destination `page.1`.
  No existing label was renamed or removed.
- `article.pdf`: rebuilt from the amended source (23 pages; the delivered
  PDF had 22). Line numbers of `article.tex` after the first insertion
  point differ from those of the delivered file.
- `data/build_validation.json`: `pdf_sha256`, `source_sha256` and
  `pdf_pages` were recomputed for the rebuilt `article.pdf` and the amended
  `article.tex`, and match the filed files; an `editorial_rebuild` field
  says so. Its other fields describe the delivered build. Any later PDF
  rebuild (`make pdf`) makes the PDF digest stale again, since pdfTeX
  embeds the build date.
- `code/verify.py`: the CSV writers pass `lineterminator='\n'` and the
  text writers `newline='\n'`, so a rerun on any platform emits LF, like
  the filed files. Rerun on a copy (`--order 70`, Windows): all four
  outputs were byte-identical to the filed files.
