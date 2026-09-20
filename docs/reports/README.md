<!-- SPDX-License-Identifier: MIT-0 -->

# Research reports

One hundred and five independent mathematical research packages, unpacked from
the
archives in which they were delivered and grouped by subject.  Each directory
holds a typeset article with its LaTeX source, a `README.md`, and in most cases
verification code together with the recorded output of running it.

**[`manifest.pdf`](manifest.pdf)** ([source](manifest.tex)) is the catalogue: it
numbers all one hundred and five reports, names the problem each one attacks and
the
result it claims, and records the archives each directory came from.  These are
AI-assisted drafts; none is refereed or machine-checked, and the manifest
records what each report claims rather than verifying it.

| Category | Reports |
|---|---:|
| [`ordinals-and-order-types/`](ordinals-and-order-types) — friendly order types, wqo powersets and statures, transfinite words, ordinal arithmetic, games, graph minors, filter sites, ideals, lattice congruences | 20 |
| [`enumerative-combinatorics/`](enumerative-combinatorics) — parking functions, pattern avoidance, preorder and order polytopes, numerical semigroups, lattice arrays, coefficient lattices, tropical degree | 19 |
| [`hankel-determinants/`](hankel-determinants) — Somos and elliptic, Catalan and ballot, Cigler's conjectures, growth and runs, arithmetic numerators | 10 |
| [`log-concavity-and-unimodality/`](log-concavity-and-unimodality) — cluster variables, chromatic coefficients, Stirling rows, independence systems, MDS codes, binomial decompositions, Bernoulli entropy | 12 |
| [`congruences-and-valuations/`](congruences-and-valuations) — supercongruences, iterated series, valuations and periodicity | 7 |
| [`surreal-numbers/`](surreal-numbers) — birthdays under multiplication, option graphs, genetic functions and gaps, evaluating formal sums | 6 |
| [`tetration-and-digit-stabilization/`](tetration-and-digit-stabilization) — congruence speed, frozen digits, `q`-Newton series | 6 |
| [`generating-functions-and-asymptotics/`](generating-functions-and-asymptotics) — Stanley's rationality question, Gregory thresholds, records, discrepancy, and nine single-sequence OEIS studies | 16 |
| [`automata-and-formal-languages/`](automata-and-formal-languages) — shuffle state complexity, DFAO reversal, synchronization, language hierarchies, additive complexity | 6 |
| [`graph-theory/`](graph-theory) — mutual visibility, domination roots, minimal dominating sets | 3 |
| **Total** | **105** |

## Rebuilding the manifest

```sh
latexmk -pdf manifest.tex && latexmk -c manifest.tex
```

## Merged reports

One hundred and twenty-five archives arrived, in seven deliveries, and yield
one hundred and five reports.  Twenty archives duplicated another: sixteen
pairs, three three-way clusters and one four-way cluster.  The seventh delivery
of eighteen produced no merge at all: the sweep checked every OEIS A-number and
every cited arXiv identifier in the tree against the eighteen, and rejected
twelve near-misses on inspection — among them three reports that all count the
terms in the derivatives of a power tower, and two that share a Bell-scale
saddle-point method on unrelated sequences.  Shared technique is not a shared
theorem.  Each cluster was merged into a
single report that proves the shared theorem once and keeps everything every
original built on top of it.  Where the originals reached a result by genuinely
different routes, every route is kept and marked as an alternative, with a
sentence on what each one buys.  The manifest names both or all source archives
on a merged entry and says what was doubled.

The largest merges:

| Merged report | Absorbed | Kept apart |
|---|---:|---|
| [`shuffle-six-state-bound`](automata-and-formal-languages/shuffle-six-state-bound) | 3 | three independent finite certifications, two of them with disjoint witness sets |
| [`preorder-q-zeta-reciprocity`](enumerative-combinatorics/preorder-q-zeta-reciprocity) | 2 | three architecturally independent proofs of the same two theorems |
| [`components-forests-and-ordinal-products`](ordinals-and-order-types/friendly-order-types/components-forests-and-ordinal-products) | 1 | two proofs of the Cartesian formula |
| [`canonical-forms-need-not-be-subgraphs`](surreal-numbers/canonical-forms-need-not-be-subgraphs) | 1 | two non-isomorphic five-vertex witnesses |
| [`multiple-chain-exponential-formula`](enumerative-combinatorics/multiple-chain-exponential-formula) | 1 | two proofs of the identity, plus eleven listed redundancies |

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
