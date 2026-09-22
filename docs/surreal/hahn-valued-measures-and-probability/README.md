# Strong Hahn Measures on Surreal Workspaces
## Atomicity, exact extension criteria, and hidden positivity obstructions

Research manuscript prepared for Vladimir Reshetnikov, 22 September 2026.

## Read the article

`article.pdf` is the compiled manuscript. `article.tex` is its complete,
standalone LaTeX source, including the bibliography. No external graphics,
BibTeX database, or private files are needed to build it.

The central results concern one explicitly fixed addition rule: a disjoint
countable family of event masses must have a well-ordered union of Hahn
supports and only finitely many contributions at each exponent.

The manuscript proves:

- Atomic representation and automatic common support on countably separated
  spaces, including an equivalent coefficientwise finite-point-atomic test.
- A necessary-and-sufficient support/finite-width criterion for coherent
  cylinder laws on countable products of finite alphabets.
- An exact support-order criterion for positivity transfer, and positive
  cylinder laws whose unique strong signed extension has a negative singleton.
- An exact independent-product criterion using individual rare entries, plus
  an example in which a binary coarse-graining extends but a prescribed
  positive three-state refinement does not.
- Transfer to actual surreal/surcomplex normal forms, and invariance of the
  extension obstructions under ordered Hahn exponent enlargement.

These are not general impossibility results for non-Archimedean probability.
Other summation/continuity axioms are explicitly distinguished.

## Build

With a TeX Live or equivalent installation providing the packages used in
`article.tex`, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `pdflatex` three times to stabilize cross-references and
contents. `build.sh` builds in a separate directory and copies the resulting
PDF to `article.pdf`.

## Exact finite checks

Python 3.10 or newer; no third-party Python packages:

```sh
python3 code/verify.py
```

The supplied run passed **5,135 assertions**, using exact rational
coefficients and lexicographically ordered rational tuple exponents. It
writes `data/verification.txt` and `data/verification.json`.

These checks verify finite identities, not infinite summability. In
particular, the finite truncation of the negative-singleton example is
positive only before its truncation depth. The proof in the article, not a
finite test, establishes positivity of every cylinder in the infinite
example. No Lean formal verification is claimed.

## Novelty and provenance

The theorems are proposed new results, with full mathematical arguments,
not independently certified priority claims. The repository audit was
pinned to commit `4cf691c7d951e037739d32d9f5c387dcce724f3c`. Its catalog,
overview, and new-archive inventory were inspected, but the interiors of
the 18 ZIP archives in `docs/new` could not all be retrieved. Consequently,
this package does **not** certify absence from every repository manuscript.
The article and `provenance.md` give the exact audit scope and literature
comparison. No previously named major conjecture is claimed solved.

The package contains no copied third-party papers, repository archives,
font files, or unverified Lean source.
