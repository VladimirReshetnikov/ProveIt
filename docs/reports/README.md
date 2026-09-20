<!-- SPDX-License-Identifier: MIT-0 -->

# Research reports

Fifty-eight independent mathematical research packages, unpacked from the
archives in which they were delivered and grouped by subject.  Each directory
holds a typeset article with its LaTeX source, a `README.md`, and in most cases
verification code together with the recorded output of running it.

**[`manifest.pdf`](manifest.pdf)** ([source](manifest.tex)) is the catalogue: it
numbers all fifty-eight reports, names the problem each one attacks and the
result it claims, and records the archives each directory came from.  These are
AI-assisted drafts; none is refereed or machine-checked, and the manifest
records what each report claims rather than verifying it.

| Category | Reports |
|---|---:|
| [`ordinals-and-order-types/`](ordinals-and-order-types) — friendly order types, wqo powersets and statures, transfinite words, ordinal arithmetic, games | 13 |
| [`hankel-determinants/`](hankel-determinants) — Somos and elliptic, Catalan and ballot, growth and runs, arithmetic Hankel numerators | 8 |
| [`congruences-and-valuations/`](congruences-and-valuations) — supercongruences, iterated series, valuations and periodicity | 7 |
| [`tetration-and-digit-stabilization/`](tetration-and-digit-stabilization) — congruence speed, frozen digits, `q`-Newton series | 6 |
| [`log-concavity-and-unimodality/`](log-concavity-and-unimodality) — cluster variables, chromatic coefficients, Stirling rows, independence systems | 7 |
| [`graph-theory/`](graph-theory) — mutual visibility, domination roots, minimal dominating sets | 3 |
| [`enumerative-combinatorics/`](enumerative-combinatorics) — parking functions, pattern avoidance, Hardinian arrays, preorder polytopes | 8 |
| [`generating-functions-and-asymptotics/`](generating-functions-and-asymptotics) — Stanley's rationality question, Gregory thresholds, records, discrepancy | 6 |
| **Total** | **58** |

## Rebuilding the manifest

```sh
latexmk -pdf manifest.tex && latexmk -c manifest.tex
```

## Merged reports

Sixty-four archives yield fifty-eight reports.  Six pairs proved the same
theorem — in five of the six by the same argument, down to shared lemmas and, in
one case, shared worked counterexamples.  Each pair was merged into a single
report that proves the shared theorem once and keeps everything both originals
built on top of it; where the two reached a result by genuinely different
routes, both proofs are kept and marked as alternatives.

| Merged report | Absorbed | Shared theorem | Proofs kept apart |
|---|---|---|---|
| [`a122251-numerators-and-denominators`](hankel-determinants/a122251-numerators-and-denominators) | `a122251-prime-exclusion-proof` | Reduced numerator of `det(1/(a+m(i+j)))` | — (one proof; the donor's unequal-steps generalization ported) |
| [`power-tower-stabilization`](tetration-and-digit-stabilization/power-tower-stabilization) | `one-stable-digit-per-height` | `T_k − T_h ≡ −2·B^h (mod B^(h+1))` | — (one proof; two headline results kept) |
| [`a348410-all-prime-congruences`](congruences-and-valuations/supercongruences/a348410-all-prime-congruences) | `a348410-cubic-supercongruence` | Odd-prime cubic supercongruence | Odd-prime and binary halves run on different mechanisms |
| [`order-types-below-omega-squared`](ordinals-and-order-types/transfinite-words/order-types-below-omega-squared) | `guarded-periodic-blocks` | `o(s_ω²(P)) = ω^(ω^(n+j(P)−2))` | Product amplification: de Jongh–Parikh, and an elementary hand proof |
| [`components-forests-and-ordinal-products`](ordinals-and-order-types/friendly-order-types/components-forests-and-ordinal-products) | `incomparability-components-and-forests` | `f(P) = \|P\| − c(Inc(P))` | Cartesian formula: corner deletion, and a chain-grid argument |
| [`mixed-base-counterexample`](generating-functions-and-asymptotics/binary-product-coefficient-counts/mixed-base-counterexample) | `mixed-base-natural-boundary` | Coefficient counts for Stanley's MO 431075 | Non-rationality: finite-state mod `p`, and the rigidity/natural-boundary route |

Three further clusters share a published target without sharing a proof, and
were left as separate reports: the two remaining friendly-order-type reports,
the two Lipparini Problem 6.2 solutions, and `finite-alphabet-transfinite-words`
(whose all-`k` theorem strictly generalizes the ω² result by a different
mechanism).

## A note on directory names

Several of these reports attack the same published problem, so each directory is
named for its own angle on it rather than for the archive it came from, and the
merged directories are named for their combined scope.  The manifest records the
original archive names with every entry.
