<!-- SPDX-License-Identifier: MIT-0 -->

# Research reports

One hundred and ten independent mathematical research packages, unpacked from
the
archives in which they were delivered and grouped by subject.  Each directory
holds a typeset article with its LaTeX source, a `README.md`, and in most cases
verification code together with the recorded output of running it.

**[`manifest.pdf`](manifest.pdf)** ([source](manifest.tex)) is the catalogue: it
numbers all one hundred and ten reports, names the problem each one attacks and
the
result it claims, and records the archives each directory came from.  These are
AI-assisted drafts; none is refereed or machine-checked, and the manifest
records what each report claims rather than verifying it.

| Category | Reports |
|---|---:|
| [`ordinals-and-order-types/`](ordinals-and-order-types) — friendly order types, wqo powersets and statures, transfinite words, ordinal arithmetic, games, graph minors, filter sites, ideals, lattice congruences | 20 |
| [`enumerative-combinatorics/`](enumerative-combinatorics) — parking functions, pattern avoidance, preorder and order polytopes, numerical semigroups, lattice arrays, tropical degree, mesh patterns, skew partitions | 21 |
| [`hankel-determinants/`](hankel-determinants) — Somos and elliptic, Catalan and ballot, Cigler's conjectures, growth and runs, arithmetic numerators | 10 |
| [`log-concavity-and-unimodality/`](log-concavity-and-unimodality) — cluster variables, chromatic coefficients, Stirling rows, independence systems, MDS codes, binomial decompositions, Bernoulli entropy | 12 |
| [`congruences-and-valuations/`](congruences-and-valuations) — supercongruences, Apéry and Motzkin congruences, iterated series, valuations and periodicity | 9 |
| [`surreal-numbers/`](surreal-numbers) — birthdays under multiplication, option graphs, genetic functions and gaps, evaluating formal sums | 6 |
| [`tetration-and-digit-stabilization/`](tetration-and-digit-stabilization) — congruence speed, frozen digits, `q`-Newton series | 6 |
| [`generating-functions-and-asymptotics/`](generating-functions-and-asymptotics) — Stanley's rationality question, Gregory thresholds, records, discrepancy, single-sequence OEIS studies, Apéry arrays | 16 |
| [`automata-and-formal-languages/`](automata-and-formal-languages) — shuffle state complexity, DFAO reversal, synchronization, language hierarchies, additive complexity | 6 |
| [`quaternionic-analysis/`](quaternionic-analysis) — slice regularity, Cauchy–Fueter analysis, the global inverse Fueter problem | 1 |
| [`graph-theory/`](graph-theory) — mutual visibility, domination roots, minimal dominating sets | 3 |
| **Total** | **110** |

## Rebuilding the manifest

```sh
latexmk -pdf manifest.tex && latexmk -c manifest.tex
```

## Merged reports

One hundred and forty-five archives arrived, in nine deliveries, and yield
one hundred and ten reports.  Two different things reduced the count, and the
difference between them is worth keeping straight.

**Duplicates.**  Twenty archives duplicated another: sixteen pairs, three
three-way clusters and one four-way cluster.  Each cluster was merged into a
single report that proves the shared theorem once and keeps everything every
original built on top of it.  Where the originals reached a result by genuinely
different routes, every route is kept and marked as an alternative, with a
sentence on what each one buys.  The manifest names all source archives on a
merged entry and says what was doubled.

**One thematic consolidation.**  Two further reports were folded into a
neighbour for a different reason — not because they repeated it, but because
they shared a subject.  The three reports on the number of terms in the
derivatives of a power tower, for `x^x` (A293239), `x^(x^2)` (A290268) and
`x^(x^x)` (A281434), are now
[`power-tower-derivative-term-counts`](generating-functions-and-asymptotics/oeis-sequence-asymptotics/power-tower-derivative-term-counts):
a common framework proved once, then the three original investigations
unabridged, then a part comparing them.  All fifty of their numbered results
survive unchanged, and a record of every edit made to the three source texts
accompanied the merge.  This was editorial, not deduplication — those three
went through the duplicate sweep first and *cleared* it, below.  Their three
theorems are three different theorems, and the merged article is at pains to say
so rather than let a shared setup suggest the answers are connected.

**The ninth delivery was ten manuscripts on one question.**  One was an
expository survey of quaternionic analysis; the other nine were independent
attempts at the same follow-up problem, all written the next day, and one of
them shipped a verbatim copy of the survey as its own source context.  They
were merged into a single article rather than catalogued as ten reports.  The
nine agree — on the two obstruction forms, on the criterion, on the affine
monodromy, on the `8m` cokernel and on the energy constant — and that agreement,
from nine separate derivations, is the substance of the entry.  Thirteen
conflicts between them were resolved and recorded; two were mathematical rather
than notational, and either would have produced a false statement in a
mechanical merge.

**The eighth delivery, by contrast, was mostly duplicates.**  Ten archives
arrived and yield six reports.  Four clusters were confirmed at proof level and
merged, one of them against a report already in the tree
([`trapezohedral-minimal-dominating-sets`](graph-theory/trapezohedral-minimal-dominating-sets),
which absorbed an incoming proof of the same A381190 conjecture).  Every
same-proof verdict was put to two adversarial challengers; one challenge
succeeded in part, and it changed the merge: the two A289587 reports refine the
same sequence by *different* statistics — excedances and records — so the merged
article keeps both refinements rather than collapsing them.  Their two local
predicates disagree on 31 of the 321-avoiders of length at most six, the
smallest being `12`.

**The seventh delivery, by contrast, produced no duplicate at all:** the sweep checked every OEIS A-number and every cited arXiv
identifier in the tree against the eighteen, and rejected twelve near-misses on
inspection — among them those same three power-tower reports, and two that
share a Bell-scale saddle-point method on unrelated sequences.  Shared technique
is not a shared theorem.

The largest merges:

| Merged report | Absorbed | Kept apart |
|---|---:|---|
| [`shuffle-six-state-bound`](automata-and-formal-languages/shuffle-six-state-bound) | 3 | three independent finite certifications, two of them with disjoint witness sets |
| [`preorder-q-zeta-reciprocity`](enumerative-combinatorics/preorder-q-zeta-reciprocity) | 2 | three architecturally independent proofs of the same two theorems |
| [`components-forests-and-ordinal-products`](ordinals-and-order-types/friendly-order-types/components-forests-and-ordinal-products) | 1 | two proofs of the Cartesian formula |
| [`canonical-forms-need-not-be-subgraphs`](surreal-numbers/canonical-forms-need-not-be-subgraphs) | 1 | two non-isomorphic five-vertex witnesses |
| [`multiple-chain-exponential-formula`](enumerative-combinatorics/multiple-chain-exponential-formula) | 1 | two proofs of the identity, plus eleven listed redundancies |

**A pair that an earlier sweep missed, checked and kept separate.**  A
crosscheck during the eighth delivery flagged
[`a348410-all-prime-congruences`](congruences-and-valuations/supercongruences/a348410-all-prime-congruences)
and
[`a352373-signed-binomial-supercongruences`](congruences-and-valuations/supercongruences/a352373-signed-binomial-supercongruences)
as possible duplicates: the second's family
`a_{r,s,t}(n) = [x^{tn}](1+x)^{rn}(1-x)^{sn}` does specialize, at `t = 1` and
`(r,s) = (-beta,-alpha)`, to the first's coefficient, and the two odd-prime
congruences then agree (the first states its modulus by the exact valuation
`v_p(N)` and the second by a declared level, but these carry the same content
once the multiplier is reindexed).

Both articles were then read in full, and **neither contains the other**.
a352373 is general in the extraction step `t`, which a348410 fixes at 1 —
a348410's "change of step" corollary varies the period `d` in `(1-x^d)`, not
the extraction index. a348410 proves, and a352373 does not: the `p = 2` case
with an exact first binary defect and its sharpness (valuation exactly
`3r-3` when both parameters are odd and `m = 1`), a single all-prime bound
`v_p >= 3r - v_p(12)` with each loss shown necessary, sharp common
denominators with both constants minimal, the primitive-cyclic-word
interpretation, a Lambert series and Euler product, algebraic generating
functions by Lagrange reversion, a spacing-three counterexample showing the
conclusion fails at `p = 5` when `1+x^2` is replaced by `1-x^3`, and a
sufficient criterion abstracting the proof beyond the family.

The proofs are also genuinely different arguments, not one argument twice:
a352373 imports Jacobsthal's congruence and uses it throughout, a348410 does
not invoke it at all and instead pairs a quadratic-tail estimate with a
coefficient estimate. **Decision: keep both.** This is the collection's
"incomparable in both directions" shape, and it is recorded here so a later
sweep does not re-litigate it.

Pairs aimed at one problem are not always duplicates, and several were kept
separate on inspection: the two Gonshor product-birthday reports prove the same
bound on domains incomparable in both directions; Cigler's Conjectures 8, 13–15
and 16 are three separate entries from one paper, as are Athanasiadis–Chapoton's
Conjectures 4.9, 5.1 and Question 4.6, Chiozini–Csernák–Soukup's Problems 1.2
and 1.3, and Deb–Sokal's clauses 1.4(c) and 1.4(d).  Three clusters share a
theorem but not a proof and were left as they are: the two remaining
friendly-order-type reports, the two Lipparini Problem 6.2 solutions, and
`finite-alphabet-transfinite-words`.

## Large regenerable artifacts

Sixteen bulk artifacts, about 79 MB in total, are deliberately not distributed:
the 200 pair-distance certificates of `dzyga-synchronizing-retract`, the four
certificate databases of `shuffle-six-state-bound`, the 76 magic-positivity
certificates of `magic-positivity-parking-polytopes`, the 1.5 M expression-DAG
records of `a158415-growth-constant`, and nine large CSV or text tables
elsewhere.  Every one is rebuilt byte for byte by its own package's
generator, each package README gives the command, and `.gitignore` keeps a
local rebuild from returning them to the history.  Nothing an article displays
depends on them: worked examples, small certificate sets and the recorded run
summaries are all still shipped.

## Notes on names and packaging

Several reports attack the same published problem, so each directory is named
for its own angle on it rather than for the archive it came from, and merged
directories are named for their combined scope.  The manifest records the
original archive names with every entry.

No package ships a checksum manifest: re-running a verification suite or
rebuilding a PDF changes file hashes, so a stored manifest goes stale on the
first rebuild.
