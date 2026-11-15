# Constructive calculus in intuitionistic primitive recursive arithmetic

This package contains a complete human-readable proof of effective versions
of both parts of the fundamental theorem of calculus and the finite-order
Euler–Maclaurin formula, together with exact-arithmetic implementations and
a detailed Lean formalization outline.

## Start here

- `report.pdf`: the complete mathematical argument, hypotheses, error bounds,
  proof-theoretic accounting, and formalization plan.
- `report.tex`: the corresponding standalone LaTeX source.
- `lean/ROADMAP.md`: concrete stages for completing the deep iPRA formalization
  using ProveIt's ConciseIPRA foundations.

## Exact scope

The results are theorem schemas in **fixed primitive recursive rational
evaluators**, with explicit arithmetic correctness promises and supplied
primitive recursive moduli. The first-order theory has number variables;
the paper does not pretend it can quantify directly over arbitrary real
functions or use a universal primitive recursive evaluator for all programs.

FTC I constructs the integral from rational sums and proves the derivative
certificate. FTC II is proved with a supplied uniform derivative modulus.
A separate version covers effective tagged-Riemann data and pointwise
derivative certificates with a supplied primitive recursive tagged-partition
realizer. The latter witness is an explicit hypothesis, not a consequence
silently extracted from qualitative differentiability or compactness.

Euler–Maclaurin has its exact cellwise Bernoulli remainder, works at every
finite order and on rational meshes, and has the elementary bound

    |R_m| <= (b-a) * 4^(-m) * M_(2m).

The paper gives a completely rational proof uniform in the order, fixing
precision before quantifier-free induction. It makes no assertion that the
infinite Euler–Maclaurin series generally converges.

## Formalization status

**The Lean source is an uncompiled candidate, not a completed formalization.**
No Lean/Lake/Elan executable was available in the preparation environment.
`lean/FiniteSkeleton.lean` contains proof scripts for finite rational
telescoping, sum inequalities, a finite FTC bound, and an alternating
recurrence, plus name interfaces. It contains no `sorry` declarations or
new axioms, but absence of those declarations does not establish that it
compiles.

Even after compiling the candidate, it will be an ambient Lean prototype.
A genuine completion must additionally construct object-theory derivations
of the form `Γ ⊢[PRAAx] φ`. The roadmap states the remaining work explicitly.
The complete mathematical arguments and exact finite validation runs are
the finished components of this package.

## Files

| File | Purpose |
| --- | --- |
| `report.tex`, `report.pdf` | Full manuscript and compiled output |
| `lean/FiniteSkeleton.lean` | Uncompiled candidate finite Lean proofs |
| `lean/ROADMAP.md` | Deep formalization plan and trust boundary |
| `code/bernoulli_em.py` | Exact rational polynomial/Bernoulli/EM implementation |
| `code/validation.json` | Recorded finite checks for that implementation |
| `code/integral_demo.py` | Canonical integral-name checks on `1/(1+x)` |
| `code/integral_validation.json` | Recorded integral/additivity/derivative checks |
| `provenance/sources.json` | Pinned repository revision and inspected sources |
| `Makefile` | Standard PDF and validation commands |
| `SHA256SUMS` | SHA-256 checksums of the package files, excluding itself |

The programs use only the Python standard library. Mathematical checks use
exact `fractions.Fraction` arithmetic. Decimal displays in the integral demo
are only displays; no decimal approximation is used as a truth oracle.

## Reproduce the checks

From this directory, with Python 3.10 or later:

```sh
python3 code/bernoulli_em.py --validate --output code/validation.json
python3 code/integral_demo.py --output code/integral_validation.json
```

The recorded run passed 382 Bernoulli checks through order 20, 85 polynomial
FTC checks, 612 unit-mesh EM checks (100 with nonzero remainder), 272 rational
mesh checks, and 600 local product-defect checks across 16 rounded-oracle
cases. The nonpolynomial integral demo passed 84 Cauchy, 20 additivity, and
96 derivative-certificate instances.

These are finite implementation/regression checks. They are not formal
proofs of the universal mathematical statements or of iPRA derivability.

## Rebuild the PDF

Use a working LaTeX installation with the usual AMS, Latin Modern,
geometry, microtype, hyperref, and table packages:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error report.tex`
three times to settle references and the table of contents. The source
does not require network access, shell escape, minted, or external figures.

## Repository baseline

Inspected ProveIt revision:

    0bf379a84212abd05e9a3f0b1320a3d7da509cf9

The corresponding toolchain is Lean `v4.32.0` and Mathlib `v4.32.0`.
The deep foundations are under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`.

The existing first-order EM theorem in
`NumberTheory/IntegerPoints/Lean/IntegerPoints/EulerMaclaurin.lean`
was inspected as a formula/sign reference. Its real-analysis, measure,
and compactness dependencies are not imported into the proposed iPRA proof.
The `docs/drafts` listing was inspected; its binary archive contents were
not audited and are not proof dependencies.

To attempt compilation of the finite Lean candidate in an already set up
checkout at the pinned revision:

```sh
lake env lean /absolute/path/to/calculus_ipra/lean/FiniteSkeleton.lean
```

This package is an archive deliverable. No commit or pull request was made
to the repository.
