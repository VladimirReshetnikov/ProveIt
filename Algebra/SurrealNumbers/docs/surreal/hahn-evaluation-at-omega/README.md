# Increasing Hahn series and surreal evaluation

Research package dated 20 September 2026.

The article gives a negative answer to Problem 7.7 in Paolo Lipparini's
*Monotone infinitary operations on ordinals (extended version)*,
arXiv:2505.00424v2 (30 April 2026), p. 38.

The source contains a formal power series B(x) with B(x)^2 = 1-x.
Any unital homomorphism sending x to omega would force a square in the
surreal ordered field to equal the negative number 1-omega. The argument
does not distribute a homomorphism over an infinite sum.

Negative coefficients are not to blame. The all-positive pair
H(x) = sum binom(2n,n)/4^n x^n and G(x) = sum x^n satisfies H^2 = G and
G = 1 + xG, so the obstruction survives on the *semiring* of
nonnegative-coefficient series, where subtraction is unavailable, and there
it already excludes every value u >= 1.

## Provenance

This package is a merge of two independently produced research reports on the
same question, `hahn-evaluation-at-omega` and `reversed-hahn-series`. Both
reached the same negative answer by the same argument — the identical
quadratic recursion for B, the identical coefficient check of B^2 = 1-x, and
the identical application of the hypothetical map to that one finite identity.
That shared core theorem is proved exactly once in the merged article. The
supporting material diverged, so this report is the union of the two toolkits
rather than a deduplication: the semiring certificate, the general
unit-square-root lemma, the elementary two-support lemma and several scope
remarks come from the second report; the infinitesimal evaluation criterion, the
order-forcing theorem, the monomial classification over an arbitrary exponent
group and the Higman appendix come from the first. Where the two reports
worded an attribution or a priority caveat differently, the more cautious
wording was kept.

## Files

- `article.pdf` — the full 28-page article, including proofs and background.
- `article.tex` — self-contained LaTeX source with an inline bibliography.
- `short-proof.pdf`, `short-proof.tex` — a one-page version of the decisive proof.
- `references.bib` — reusable metadata for the six references.
- `code/verify.py` — exact finite regression checks; standard Python library only.
- `results/verification.json` — the executed verification report.
- `results/coefficients.csv` — 257 rows, degrees 0–256, with exact coefficients
  of both B(x) and H(x) and the computed coefficients of B(x)^2 and H(x)^2.
- `proof-audit.md` — assumptions, scope, and potential logical pitfalls.
- `sources.md` — version-specific sources and the priority-search boundary.
- `build.sh` — POSIX shell script that runs the checks and builds both PDFs.

## Main results

1. No ring homomorphism from the stated increasing-support Hahn class into
   the surreals can send every x^a to Conway's omega^a. Already the prescribed
   image x -> omega is impossible on Q[[x]].
2. The same obstruction holds over the semiring Q_{>=0}[[x]] of
   nonnegative-coefficient series, with no additive inverses in the source, and
   there it excludes every value u >= 1 rather than only u > 1. This implies
   result 1 by restricting any proposed ring map. Conversely, every semiring
   map to a ring extends uniquely to Q[[x]] by writing each rational series
   as a difference of two nonnegative-coefficient series. The article proves
   this correspondence and retains the positive witness as a separate
   elementary proof.
3. The possible images of x under unital homomorphisms Q[[x]] -> No are
   exactly the surreal infinitesimals, including zero. Each such value has a
   coefficient-fixing strongly additive evaluation on R[[x]].
4. For an ordered exponent group G, a prescription x^a -> omega^{f(a)}
   admits a unital Hahn-field homomorphism exactly when f is additive and
   strictly order-reversing. In that case the coefficient-fixing strongly
   additive extension exists and is unique within that class of maps.
5. The classical exponent-reversing map sends sum r_a x^a to
   sum r_a omega^{-a}; it is not the prescription requested in the problem.

The normal-form results, Hahn-field background, formal binomial series,
Higman's lemma, and exponent-reversing embedding are classical. The paper
identifies those ingredients rather than claiming them as new.

## Correction to the comparison of the proofs

The earlier article and audit called the ring and semiring obstructions
“incomparable.” That was incorrect: the target of the semiring map is the
whole ordered field, so restricting a ring map automatically has the
required codomain. The revised comparison also proves the converse extension
explicitly. If `a-b = a'-b'`, then `a+b' = a'+b`; applying the semiring map
makes `ψ(a)-ψ(b)` independent of the chosen representation. Addition and
multiplication then give a unique ring homomorphism.

The two witness proofs themselves are unchanged. The positive pair `H, G`
provides a direct semiring certificate, while `B² = 1-x` gives the shorter
ring argument. The standalone short proof remains valid and makes no claim
of logical incomparability. The correction is also recorded in
[`proof-audit.md`](proof-audit.md).

## Substitution, topology, and extension criteria

The infinitesimal criterion permits a general surreal series as the value
of `x`. Its finite-word proof controls every coefficient of every power and
justifies their regrouping. Only the pure monomial case `x -> omega^a`,
`a < 0`, reduces to an exponent change. The earlier description of the whole
construction as a change of value group was too narrow.

The geometric partial sums of `sum omega^(-n)` fail to converge in the full
surreal order topology, because every tail exceeds `omega^(-omega)`. They
do converge in the intrinsic order topology of `R((omega^(-1)))`: each
positive radius there has an integer leading exponent, eventually exceeded
in smallness by the tail. The earlier phrase “in any order-theoretic sense”
was therefore too broad. Hahn summability itself requires neither topology.

The pure monomial criterion applies to arbitrary ordered abelian exponent
groups, without a divisibility assumption. Its constructed map preserves
the leading coefficient and hence the canonical order. For a simple
algebraic extension of `R(x)`, extending embeddings correspond exactly to
the surreal roots of the evaluated minimal polynomial; the image of its
generator determines the extension. These are separate existence criteria,
not a classification of all abstract Hahn-field embeddings.

## Run the exact checks

Python 3.9 or later; no package installation or internet access is required.
From this directory:

```text
python code/verify.py --degree 256 --trials 1000 --output results
```

The default run, modulo x^257 throughout:

- verifies B(x)^2 = 1-x, H(x)^2 = G(x), B(x)H(x) = 1, and (1-x)G(x) = 1;
- compares 257 coefficients of B from five independent routes — the quadratic
  recursion, the general unit square-root recursion, the first-order binomial
  recursion, the Catalan closed formula, and Catalan numbers regenerated by the
  convolution recurrence C_m = sum C_i C_{m-1-i};
- checks the signs, that every coefficient of B is dyadic, that every
  coefficient of H is strictly positive, and both differential recurrences
  2(n+1)b_{n+1} = (2n-1)b_n and 2(n+1)h_{n+1} = (2n+1)h_n;
- verifies 32 scaled unit-square identities for 1 +- nx, 1 <= n <= 16, and 12
  square roots of units 1 + cx at signed rational c in
  {+-1, +-2, +-3, +-1/2, +-2/3, +-7/5}, all through degree 64;
- runs 1000 deterministic sparse-polynomial trials at random positive rational
  exponent scales with seed 20260920, and a second harness with seed 1729 of
  200 Laurent-polynomial pairs at each of the three fixed scales 1, 2, 3/2,
  that is 600 scale/pair cases.

Every reversal case checks addition, multiplication, and strict reversal of the
support order. There is no floating-point calculation. Explicit checks use a
`require` helper raising `VerificationFailure`, so they remain enabled under
`python -O`; a failure prints a `FAIL` line and exits nonzero.

Optional flags: `--degree`, `--trials`, `--fixed-pairs`, `--seed`, `--output`.
The first three reject nonpositive values.

```text
python code/verify.py --degree 512 --trials 300 --fixed-pairs 50 --output results
```

These are finite regression tests, not a proof of the infinite statements.
The complete coefficient-recursion proof and the summability proofs are
in the article. No Lean, other proof assistant, or surreal arithmetic kernel
was used.

## Build the PDFs

A reasonably complete TeX Live or MiKTeX installation is sufficient. The
sources use the Palatino-style `newpx` text and math fonts, AMS mathematics,
`mathtools`, `microtype`, `geometry`, `booktabs`, `tabularx`, `array`,
`enumitem`, `titlesec`, `fancyhdr`, `tcolorbox`, `listings`, `natbib`, `xurl`,
`hyperref` and `cleveref`. No font files or external figures are included or
required. No separate BibTeX run is needed: the references are included
directly in `article.tex`. The `.bib` file is supplied for reuse, not as a
build dependency.

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error short-proof.tex
```

Alternatively run `sh build.sh`. It first runs the exact checks and stops if
they fail, then builds with `latexmk` when available, keeping intermediate
files in `build/` and copying the completed PDFs here; where `latexmk` is
absent it falls back to three plain `pdflatex` passes per document.

## Research-status qualification

The question is explicit in the latest inspected arXiv revision. A focused
public-source search on 20 September 2026 did not locate a prior resolution.
This is not a guarantee of priority and does not exclude unpublished or
unindexed observations. The proofs were developed and reviewed during this
session, but have not been independently refereed or proof-assistant checked.

The result answers the explicit monomial-normalized ring-homomorphism
question. It does not settle Lipparini's broader Problem 7.5 about infinitary
operations on arbitrary surreal sequences or on games: a partial operation, an
operation on a smaller domain, or an operation that is not required to be
multiplicative evades this obstruction entirely.

Two references carried over from the merged manuscript — Kaplan, Krapp and
Serra (arXiv:2509.22374v1) and Bournez and Guilmant (arXiv:2201.08199) — are
cited for standard background only and were not independently re-inspected
while preparing this package. See `sources.md`.

The package contains no external papers or font files. The PDF uses normally
embedded subsets of the TeX installation's fonts.
