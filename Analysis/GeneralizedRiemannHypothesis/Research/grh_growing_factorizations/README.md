# Small-prime factorizations at arbitrary retained density

Research note, 27 November 2026. The input is Dirichlet GRH as exported by the pinned vendored grh-lean development. This packet extends the ProveIt article's fixed-number-of-labels minority-density factorization theorem to a growing number of labels, at the optimal order of growth for logarithmic quotas and log-squared prime height.

## Files

- `paper.tex` — full LaTeX manuscript, self-contained except for standard analytic number theory results cited in the bibliography.
- `paper.pdf` — compiled nine-page manuscript.
- `check.py` — standard-library Python implementation of the type-product repair lemma, exact dynamic program and finite tests.
- `checks.txt` — actual test output (504 randomized repair instances, 75 exhaustive DP comparisons, one large-cycle fixture and a mod-7 example).
- `source_audit.md` — source provenance, status and proof dependency map.
- `Makefile` — commands to reproduce the PDF and tests.
- `SHA256SUMS` — integrity hashes of the payload.

## Reproduce

Use a standard TeX Live distribution (`pdflatex`, AMS packages, Latin Modern, hyperref, microtype) and Python 3.9 or newer.

```sh
make pdf
make check
sha256sum -c SHA256SUMS
```

Check the hashes before rebuilding: rebuilds can change PDF metadata. No external Python packages are needed. The tests are exact finite checks; they do not establish the GRH estimate. No Lean build of this new theorem was run. The pool existence proof is probabilistic, not a certified concrete list for a supplied numerical Q. Constants are not optimized. No repository changes were made.

## Main novelty claim

Theorem 2.1 is a proved implication of Dirichlet GRH and standard analytic estimates. Two improvements over Article/sections/dir.tex are (i) comparison of bounded words in pairwise ratios, so that only moduli at most Q^(4 floor(1/a)) are needed, and (ii) type-count transportation-cycle compression, bounding repair cost by O_a(r) rather than by an exponentially large quotient order. This permits exact support and relative error Q^(-A) at r on the scale log Q / log log Q for every fixed retained density a>0. The quotient index and worst-case support fraction are sharp. Priority relative to all published and unpublished mathematics has not been established; the comparison with the directly relevant merged-article results is documented.
