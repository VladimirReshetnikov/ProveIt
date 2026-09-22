# Finite Recurrences versus Surreal Scale

**Holonomic rigidity and a sharp dilation criterion for entire Hahn functions**
Research manuscript, 22 September 2026.

## Main results

Let K = C((t^Gamma)), with Gamma a fixed nonzero set-sized ordered abelian
group. "Entire" means that the defining power-series family is strongly Hahn
summable at every point of K, not at every point of the full surcomplex class.

Theorem A proves that every entire D-finite power series is a polynomial.
It gives a stronger uniform conclusion: a fixed differential operator has
an exterior valuation region where strong evaluation of any formal solution
already forces a polynomial with a common degree bound.

Theorem B gives an exact existence criterion for an infinite-order dilation q:
a nonpolynomial entire solution of a nonzero linear polynomial-coefficient
q-difference equation exists if and only if |v(q)| is an order unit of Gamma.
An order unit is a positive element whose integer multiples are cofinal in
the entire value group. Positive valuation alone is insufficient in higher rank.
The proof includes unit dilations whose residues are roots of unity.

Theorem C extends differential rigidity to jointly D-finite series in finitely
many variables. Further results cover mixed differential-dilation operators
at nonzero noncofinal scales and an explicit entire series on the surreal
workspace with exponent group direct-sum_{j>=0} Q*omega^j. That series satisfies
no pure differential equation and no pure dilation equation for any
infinite-order dilation in its workspace.

## Files

- `article.pdf`: the 22-page article, with proofs and references.
- `article.tex`: standalone LaTeX source with an embedded bibliography.
- `code/verify.py`: standard-library exact-arithmetic checks.
- `data/verification.txt`: recorded run, 3,705 checks passed, none failed.
- `data/build_report.txt`: compilation and PDF inspection record.
- `SOURCES_AND_SCOPE.md`: sources consulted, repository pin, and priority limits.
- `PROOF_AUDIT.md`: assumptions and the critical steps of the proof review.
- `SHA256SUMS.txt`: checksums of the delivered files except this checksum file.

## Build and reproduce

With a conventional TeX Live or MiKTeX installation and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

No BibTeX, external images, shell escape, or repository checkout is needed.
The source names all required LaTeX packages, including `newtx`, `microtype`,
`xurl`, and `hyperref`.

With Python 3.9 or later:

```sh
python code/verify.py --output data/verification-rerun.txt
```

No third-party Python packages are needed. The output argument is required.
Integer and rational arithmetic are exact; no floating-point approximations
are used. A failed check raises an error and prevents a successful report.

## Status

This is an AI-assisted research manuscript with written mathematical proofs.
The all-rank classification is offered as a proposed original contribution,
not as certified bibliographic priority or a solution of a named published
conjecture. The targeted literature review did not establish exhaustive priority.
No independent refereeing or proof-assistant verification is claimed.

The finite checks validate coefficient conversions, identities, cancellation
examples, and finite ordered-group examples. They do not establish the infinite
support arguments, cofinality claims, generic-line theorem, or nonexistence of
annihilating operators. Those conclusions rely on the proofs in the article.

All variable derivatives annihilate the Hahn coefficients. They are not the
Berarducci-Mantova scalar derivation. Finite-order dilations are explicitly
excluded from the main dilation theorem. No nonlinear differential
transcendence claim is made. The original repository was not modified.
