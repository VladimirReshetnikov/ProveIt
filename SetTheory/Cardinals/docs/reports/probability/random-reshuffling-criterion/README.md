# An Exact Small-Step Criterion for Random Reshuffling

**Research draft, October 8, 2026.** The article studies actual one-block expected
squared errors for symmetric quadratic component losses with a common minimizer.
It supplies self-contained proofs, not merely numerical counterexamples.

## Main result

Let H be the mean component Hessian, V = average((H_i-H)^2), and K = ker(V).
For every fixed block length 2 <= m <= n and fixed positive position-dependent
step weights, without-replacement sampling eventually improves expected squared
Euclidean error for **every** initial state if and only if H preserves K.

When preservation fails, the smallest eigenvalue of the with-replacement minus
without-replacement Gram matrix is negative at order eta^4, with an exact leading
coefficient. The article gives a positive rank-one least-squares consequence,
a minimal rank-two strongly convex obstruction, a fixed-state objective reversal,
explicit rational thresholds, and an exact polynomial-time classification routine.

These are one-block, fixed-input, small-step results. They are not a new SGD
convergence rate, a multi-epoch theorem, or a claim that one sampling law is
universally preferable. Historical novelty and independent peer review remain
unconfirmed. See `CLAIMS.md` for precise boundaries.

## Read and build

Read `article.pdf`. The complete LaTeX source is `article.tex`; bibliography
entries are embedded, so BibTeX is not required. `references.bib` is provided
separately for integration with other manuscripts.

```sh
./build.sh
```

The build requires a LaTeX installation with pdflatex, Latin Modern, amsmath,
amsthm, mathtools, microtype, booktabs, enumitem, fancyhdr, listings, hyperref,
and cleveref. It writes auxiliary files only into `build/` and copies the
completed PDF to `article.pdf`.

## Reproduce the exact checks

Tested environment: Python 3.13.5, SymPy 1.14.0. Python 3.10 or newer is needed
for the included type syntax and bit-count operation. Only the tested environment
is claimed as verified.

```sh
python -m pip install -r requirements.txt
python tests/verify.py
python tests/explicit_example.py
```

The main suite recorded **1,291 passing assertions**, including 90 coefficient
fixtures, six direct-enumeration cross-checks, eight rank-one fixtures, rational
certificate checks, and a degree-six polynomial identity. It writes
`results/verification.json`, `certificates/diagnostic_examples.json`, and
`certificates/schedule_identity.json`. Timing is environment-dependent and is not
an asymptotic speed claim.

`tests/explicit_example.py` uses only the standard library. It independently
enumerates the four with-replacement paths and two without-replacement paths,
checks exact gaps, and writes `results/explicit_gaps.csv` and
`results/explicit_example.json`. Decimal eigenvalues in the CSV are displays,
not premises of any exact assertion. The full intervals of validity are proved
in the article, not inferred from a finite test grid.

No Lean, Isabelle, Coq, or other proof-assistant verification is claimed.

## Classify a rational instance

```sh
python code/classify.py certificates/two_component_input.json \
    --output certificates/two_component_certificate.json
```

Input has `hessians` (equal-size symmetric matrices) and `weights` (length m).
Use integers or rational strings such as `"3/7"`; floats and booleans are rejected.
For example:

```json
{
  "hessians": [[[3, 1], [1, 2]], [[1, 1], [1, 2]]],
  "weights": [1, 1]
}
```

Output is one of `identical`, `eventual_domination`, or `eventual_reversal`.
It includes exact mean/variance/kernel data. Nontrivial branches include a
positive rational step threshold. The reversal branch supplies the two rational
vectors defining the affine witness x(eta) = v + eta*w.

The classifier validates symmetry, not convexity. The matrix theorem holds for
symmetric inputs; to interpret it as convex optimization, positive semidefiniteness
must also be checked. The example Hessians are positive definite by the explicit
eigenvalue proof in the article.

The diagnostic uses polynomial-time exact linear algebra. The expectation
routines in `code/exact_matrices.py` are separate verification utilities and
include exponential subset/path computations. They are **not** the proposed
polynomial-time diagnostic and are intended only for small instances.

## Provenance and integration

`SOURCES.md` records the inspected repository revision and the primary literature.
No result from the OpenAI manuscript collection is assumed in the proofs.
The package does not modify any remote repository. Preserve the claim boundaries
and verification qualifications when integrating these files into another project.
`SHA256SUMS` records the delivered file contents (excluding the checksum file itself).
