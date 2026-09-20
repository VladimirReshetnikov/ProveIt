# Cofinal strata and ordinal absorption
## Finitary powersets of finite lexicographic sums

Research article and reproducible calculations, 19 September 2026.
Prepared for Vladimir Reshetnikov with ChatGPT.

## Result and scope

The article develops a concrete partial answer to the extension question in
Abriola et al., *Measuring well-quasi-ordered finitary powersets*, Section 6,
p. 23 (arXiv:2312.14587v2).

Let K(P) be the finitely generated downsets of P, including the empty downset,
ordered by inclusion. For a finite nonempty poset Q, replace each q by an
ordinal chain alpha = omega^rho, rho > 0, and order distinct fibers according
to Q. Call this S_alpha(Q). Let M(Q) be the inclusion-maximal antichains of Q,
ordered by Hoare domination. The proved formulas are

    o(K(S_alpha(Q))) = sum, in decreasing k, omega^(rho natural-product k) c_k(Q)
    h(K(S_alpha(Q))) = alpha * height(M(Q)).

Here c_k counts size-k maximal antichains not dominated by a larger maximal
antichain. The sum and the multiplication in the height formula are ordinary
ordinal operations.

The general maximal-order-type theorem permits nonuniform WPO fibers with
known pure values o(K(P_q)) = omega^beta_q. Positive purity implies that there
is no finite cofinal subset of a fiber. The theorem is proved by a finite
cofinal-stratification argument, not by extrapolating numerical samples.

The article does NOT claim a general width formula, a nonuniform height
formula, or arbitrary closure under repeated finitary powersets. Novelty has
not been independently established. Uniform lexicographic products already
have a published 2025 treatment; that solved problem is not presented as open.

## Contents

| File | Purpose |
| --- | --- |
| `article.pdf` | Complete 20-page research article, including proofs and references |
| `article.tex` | Main editable LaTeX source; diagram is native TikZ |
| `references.tex` | Bibliography included directly by the article |
| `references.bib` | The same bibliography in reusable BibTeX format |
| `code/ordinals.py` | Exact hereditary Cantor normal forms below epsilon_0 |
| `code/frontiers.py` | Finite-poset invariants, frontier formula, CLI, lex-sum formula |
| `code/verify.py` | Deterministic finite verification suite |
| `data/verification.json` | Recorded verification outcome and case counts |
| `data/poset_census.csv` | All 5,231 naturally labelled posets through six vertices |
| `data/*.json` | Sample inputs and outputs |
| `PROOF_AUDIT.md` | Assumptions, dependencies, and boundaries of the proofs |
| `SOURCES.md` | Literature and status-check record |
| `build.py` | Optional cross-platform build helper |

No Python packages need to be installed. The reference implementation requires
Python 3.10 or later and was tested with Python 3.13.5. The mathematics allows
arbitrary ordinal exponents; the executable notation system is deliberately
limited to ordinals below epsilon_0.

## Run the calculations

From the extracted project directory:

```sh
python code/verify.py
python code/frontiers.py
python code/frontiers.py data/N.json
python code/frontiers.py data/weighted_N.json
python code/frontiers.py data/natural_exponent.json
python code/frontiers.py data/lexicographic_tails.json
```

The N example gives maximal type `omega^2*3` and height `omega*3`. The weighted
N example gives maximal type `omega^5 + omega^3`. The natural-exponent example
uses rho = omega + 1 and gives `omega^(omega*2 + 2)`. The last example concerns
the lexicographic sum itself, NOT its finitary powerset, and gives `omega*2 + 2`.

The verifier regenerates its report and census. It checks 216,386 assertions,
including 5,231 uniform skeletons, 3,450 weighted frontier cases, 3,450 general
pure-stratum cases, 3,450 nonuniform lexicographic CNF cases, and 39,370 profile
pairs. The run time and Python version may differ on another machine.

These are finite structural and implementation tests, not a Lean formalization
or a computation of infinite bad-sequence-tree ranks. The article contains the
separate transfinite proofs.

## JSON input

Vertex labels are integers 0 through n-1. An edge [i,j] means i < j; Hasse edges
are enough because the program computes transitive closure. Cycles are rejected.

Choose at most one of the following mode fields:

| Field | Meaning |
| --- | --- |
| `rho` | Uniform fibers omega^rho; computes both powerset maximal type and height. Defaults to 1. |
| `fiber_exponents` | Values beta_q such that o(K(P_q)) = omega^beta_q; computes only powerset maximal type. |
| `fiber_types` | Values o(P_q); computes the maximal type of the lexicographic sum itself. Zero fibers are allowed. |

A finite ordinal is a nonnegative JSON integer. Any other ordinal is a list of
`[exponent, positive_coefficient]` pairs in strictly decreasing exponent order.
Exponents use the same recursive representation. Thus

```json
[[1,1],[0,1]]
```

represents omega + 1. Ordinary addition is `a + b` in the Python API, whereas
natural sum and product use the explicit methods `natural_sum` and
`natural_product`. No floating-point arithmetic is used.

## Rebuild the article

A standard TeX installation with pdfLaTeX, New PX fonts, AMS packages, TikZ,
tcolorbox, natbib, hyperref, listings and the other packages named in the
preamble is sufficient. Font files are supplied by the TeX installation.

```sh
latexmk -pdf article.tex
```

or run `pdflatex article.tex` three times. BibTeX is NOT required: the article
includes `references.tex` directly. The `.bib` file is supplied for reuse.

The optional helper first runs the verifier, then uses latexmk or falls back
to three pdfLaTeX passes:

```sh
python build.py --verify
```

## A boundary worth retaining

For an isolated omega^2 fiber beside two successive omega fibers, the frontier
poset is a two-element chain and both strata have height omega^2. Nevertheless,
the whole finitary powerset has height omega^2, not omega^2*2. Its persistent
large coordinate cannot be reset between strata. The article proves this
counterexample and explains why the uniform height construction avoids it.
