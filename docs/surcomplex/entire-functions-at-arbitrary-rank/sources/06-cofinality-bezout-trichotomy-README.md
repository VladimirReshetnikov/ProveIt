# Cofinality, Factorization, and Bézout Failure for Entire Surcomplex Hahn Functions

**A classification at arbitrary set-sized valuation rank**

Research draft prepared for Vladimir Reshetnikov, 21 September 2026.
The article is 26 pages, with 29 numbered theorems, lemmas, propositions,
and corollaries, an internal bibliography, and full mathematical proofs.

## Principal results

The coefficient field is K_Gamma = C((t^Gamma)), where Gamma is a set-sized
**divisible ordered abelian group** and C has the trivial valuation. Entire
means that the power series is strongly Hahn-summable at every point of this
fixed field, not at every point of the full proper class No[i].

Theorem 1.2 classifies its ring E_Gamma:

- Uncountable cofinality: E_Gamma is the polynomial ring, hence a PID.
- A positive element with cofinal integer multiples: E_Gamma is a
  non-Noetherian Bézout domain, with arbitrary radially discrete Hermite
  interpolation.
- Countable cofinality without such an element: E_Gamma is a non-Noetherian
  GCD domain, but not a Bézout domain. An explicit two-generated proper ideal
  has no common zero.

The zero group gives C[Z] by the strong-summation convention.

The strongest proposed original result is Theorem 7.4. For a cofinal sequence
of positive scales gamma_n with gamma_(n+1) greater than every finite multiple
of gamma_n, set rho_n = t^(-gamma_n) and
sigma_n = t^(-gamma_n) + t^(gamma_(n+1)). The two canonical products with roots
rho_n and sigma_n have disjoint simple zero sets and greatest common divisor
1, but admit no entire A, B with A f + B g = 1.

Other results include the exact coefficient criterion (Theorem 3.1),
support-controlled preparation (Theorem 4.3), arbitrary-rank root counts and
canonical products (Theorems 5.2, 6.3, 6.4), and the sharp workspace-extension
criterion (Theorem 10.1). Corollary 10.2 proves that enlarging the Hahn field
cannot repair the counterexample while keeping both functions entire.

## Status and scope

These are proposed original contributions with mathematical proofs, not a
claimed solution of a named published conjecture. The literature check was
targeted, not exhaustive; priority is not certified. Classical rank-one
factorization and Hahn-field results are credited. The paper and proofs have
not been independently refereed or checked in a proof assistant.

The source review distinguishes this function ring from the repository's
ordinary-holomorphic-coefficient Hahn sheaves and from arbitrary fine-local
surcomplex functions. See Appendix C and research_audit.md. No repository
files have been modified.

## Contents

- article.pdf — the complete 26-page article.
- article.tex — standalone LaTeX source, including the bibliography.
- verify_examples.py — exact finite checks, Python 3.10+, standard library only.
- verification.json — the delivered run: 831 checks, all passed.
- research_audit.md — source scope, snapshot, novelty and proof-status notes.
- build_report.json — final compilation and PDF validation record.
- build.sh — convenience build and optional finite-check command.

The 831 checks verify finite formulas, finite preparation recursions and
inverse jets. They do **not** prove the infinite support, cofinality,
factorization, or nonexistence theorems. Finite truncations of the
counterexample are coprime polynomials and do have polynomial Bézout identities.

## Build

A normal TeX Live or MiKTeX installation with the packages in article.tex and
latexmk is sufficient. No BibTeX, external graphics, shell escape, fonts supplied
as separate files, or repository checkout is needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Or use `sh build.sh`. To rebuild and repeat the finite checks:

```sh
sh build.sh --check
```

The latter writes verification.recheck.json, preserving the delivered record.
For a check without rebuilding the article:

```sh
python3 verify_examples.py --output /tmp/surcomplex-verification.json
```

The script uses exact rational arithmetic and seed 20260921. It requires no
network access or third-party Python packages.
