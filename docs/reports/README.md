<!-- SPDX-License-Identifier: MIT-0 -->

# Research reports

Seventy-one independent mathematical research packages, unpacked from the
archives in which they were delivered and grouped by subject.  Each directory
holds a typeset article with its LaTeX source, a `README.md`, and in most cases
verification code together with the recorded output of running it.

**[`manifest.pdf`](manifest.pdf)** ([source](manifest.tex)) is the catalogue: it
numbers all seventy-one reports, names the problem each one attacks and the
result it claims, and records the archives each directory came from.  These are
AI-assisted drafts; none is refereed or machine-checked, and the manifest
records what each report claims rather than verifying it.

| Category | Reports |
|---|---:|
| [`ordinals-and-order-types/`](ordinals-and-order-types) — friendly order types, wqo powersets and statures, transfinite words, ordinal arithmetic, games, graph minors, filter sites | 18 |
| [`surreal-numbers/`](surreal-numbers) — birthdays under multiplication, option graphs, genetic functions and gaps, evaluating formal sums | 6 |
| [`hankel-determinants/`](hankel-determinants) — Somos and elliptic, Catalan and ballot, growth and runs, arithmetic Hankel numerators | 8 |
| [`congruences-and-valuations/`](congruences-and-valuations) — supercongruences, iterated series, valuations and periodicity | 7 |
| [`tetration-and-digit-stabilization/`](tetration-and-digit-stabilization) — congruence speed, frozen digits, `q`-Newton series | 6 |
| [`log-concavity-and-unimodality/`](log-concavity-and-unimodality) — cluster variables, chromatic coefficients, Stirling rows, independence systems | 7 |
| [`graph-theory/`](graph-theory) — mutual visibility, domination roots, minimal dominating sets | 3 |
| [`enumerative-combinatorics/`](enumerative-combinatorics) — parking functions, pattern avoidance, Hardinian arrays, preorder and order polytopes | 10 |
| [`generating-functions-and-asymptotics/`](generating-functions-and-asymptotics) — Stanley's rationality question, Gregory thresholds, records, discrepancy | 6 |
| **Total** | **71** |

## Rebuilding the manifest

```sh
latexmk -pdf manifest.tex && latexmk -c manifest.tex
```

## Merged reports

Eighty archives arrived, in three deliveries, and yield seventy-one reports.
Nine pairs proved the same theorem.  Each pair was merged into a single report
that proves the shared theorem once and keeps everything both originals built on
top of it; where the two reached a result by genuinely different routes, both
proofs are kept and marked as alternatives.

| Merged report | Absorbed | Shared theorem | Kept apart |
|---|---|---|---|
| [`a122251-numerators-and-denominators`](hankel-determinants/a122251-numerators-and-denominators) | `a122251-prime-exclusion-proof` | Reduced numerator of `det(1/(a+m(i+j)))` | three evaluation routes; two proofs of the numerator formula |
| [`power-tower-stabilization`](tetration-and-digit-stabilization/power-tower-stabilization) | `one-stable-digit-per-height` | `T_k − T_h ≡ −2·B^h (mod B^(h+1))` | — (one proof; two headline results) |
| [`a348410-all-prime-congruences`](congruences-and-valuations/supercongruences/a348410-all-prime-congruences) | `a348410-cubic-supercongruence` | Odd-prime cubic supercongruence | odd-prime and binary halves run on different mechanisms |
| [`order-types-below-omega-squared`](ordinals-and-order-types/transfinite-words/order-types-below-omega-squared) | `guarded-periodic-blocks` | `o(s_ω²(P)) = ω^(ω^(n+j(P)−2))` | product amplification: de Jongh–Parikh, and an elementary hand proof |
| [`components-forests-and-ordinal-products`](ordinals-and-order-types/friendly-order-types/components-forests-and-ordinal-products) | `incomparability-components-and-forests` | `f(P) = \|P\| − c(Inc(P))` | Cartesian formula: corner deletion, and a chain-grid argument |
| [`mixed-base-counterexample`](generating-functions-and-asymptotics/binary-product-coefficient-counts/mixed-base-counterexample) | `mixed-base-natural-boundary` | Coefficient counts for Stanley's MO 431075 | non-rationality: finite-state mod `p`, and the rigidity route |
| [`ordinal-chomp-transition-at-two`](ordinals-and-order-types/games-on-ordinals/ordinal-chomp-transition-at-two) | `ordinal-chomp-winner-stability` | `ch(⟨4,6,9⟩) = 2`, opening `ω·4+4` | poisoned and unpoisoned conventions, reconciled by a dictionary |
| [`hahn-evaluation-at-omega`](surreal-numbers/hahn-evaluation-at-omega) | `reversed-hahn-series` | No ring map sending `x^a` to `ω^a` | a nonnegative-coefficient semiring obstruction with weaker hypotheses |
| [`canonical-forms-need-not-be-subgraphs`](surreal-numbers/canonical-forms-need-not-be-subgraphs) | `sparse-option-graphs` | Canonical forms need not be subgraphs | two different five-vertex witnesses, two odd-cycle families, two high-girth constructions |

Pairs aimed at one problem are not always duplicates.  The two Gonshor
product-birthday reports prove the same bound on domains that are incomparable
in both directions, so neither theorem contains the other and both are kept; on
their common corner `R[[ω^(-1)]]` the result is proved twice by the same
mechanism.  Several other pairs answer *different* numbered problems of one
paper — Problem 1.2 against 1.3 of Chiozini–Csernák–Soukup, Conjecture 5.1
against 7.2/4.2/4.4 of Athanasiadis–Chapoton — and are likewise separate.
Three clusters share a theorem but not a proof and were left as they are: the
two remaining friendly-order-type reports, the two Lipparini Problem 6.2
solutions, and `finite-alphabet-transfinite-words`.

## Notes on names and packaging

Several reports attack the same published problem, so each directory is named
for its own angle on it rather than for the archive it came from, and merged
directories are named for their combined scope.  The manifest records the
original archive names with every entry.

No package ships a checksum manifest: re-running a verification suite or
rebuilding a PDF changes file hashes, so a stored manifest goes stale on the
first rebuild.
