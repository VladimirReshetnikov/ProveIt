<!-- SPDX-License-Identifier: MIT-0 -->

# Two formalization projects in set theory and computability

This repository holds two independent research projects that grew in the same style
— a research plan, a series of independent research reports, a deduplicated
synthesis, and a Lean 4 formalization — and that share a toolchain, a Mathlib
revision and the `ProveIt` dependency.  They were merged into one repository in
September 2026; the history of both is preserved.

| | Subject | Lean library | Documents |
|---|---|---|---|
| **Large cardinals** | Exacting, ultraexacting and cover-exacting cardinals at the inconsistency frontier | `Cardinals/` | `docs/cardinals/` |
| **Coarse degrees** | Coarse Turing equivalence, and the failure of C1 | `CoarseDegrees/` | `docs/coarse-degrees/` |

The two are mathematically independent.  They do share a technical layer: both use
`ProveIt`'s first-order syntax (`SetTheory.Form`, `Sat`) and, on the set-theoretic
side, its internal-satisfaction machinery.

Alongside them, `docs/reports/` collects one hundred and eleven further research reports on
unrelated topics, with no Lean counterpart; see [Other research
reports](#other-research-reports).

## Large cardinals

Thirty-six continuation reports, delivered in four rounds of nine, on cover-exacting,
exacting and ultraexacting cardinals.  `docs/cardinals/research-synthesis/` merges them
into one document, stating each result once in the strongest form reached by any report,
with a source tag and a concordance; `docs/cardinals/research-notes/` holds a note on
virtually exacting cardinals and large countable ordinals, written here rather than
supplied.  `Cardinals/` formalizes the parts that are theorems of ZFC about a single
witness, admitting published results with citations; `Cardinals/README.md` has the
coverage table and the list of admitted statements.

The strongest result is that, in ZFC, a cover-exacting cardinal cannot lie between two
strongly compact cardinals — a partial negative answer to a problem of Blue and Goldberg.

## Coarse degrees

Ten research reports on coarse Turing equivalence, nine of them attacking the statement
**C1** — every nonuniform coarse-equivalence class contains a representative of least
Turing degree, the coarse instance of Question 7 of Gerdes — which is false.
`CoarseDegrees/` proves `¬ C1`, `¬ C1Uniform` and a third independent route through
dyadic codes, and formalizes report 10 on coarse hyperdegrees and the failure of
Martin's cone theorem for the coarse degrees.  See `CoarseDegrees/README.md`.

## Other research reports

`docs/reports/` holds one hundred and eleven independent reports that belong to neither project
and are not formalized here: ordinals and well-quasi-orders, surreal numbers, Hankel
determinants, supercongruences, tetration and digit stabilization, log-concavity,
graphs, automata and formal languages, enumerative combinatorics,
generating-function asymptotics, and quaternionic analysis.  Most attack a
specific conjecture from the literature or from an OEIS entry; about a quarter are
counterexamples rather than proofs.  They arrived as one hundred and fifty-four
archives in ten deliveries; twenty-four of them duplicated another and were
merged away, and two more were folded into a neighbour on grounds of shared
subject rather than duplication.  Every merged report keeps every original's extra
material and, where the proofs genuinely differed, every proof.
`docs/reports/manifest.pdf` catalogues all one hundred and eleven, and `docs/reports/README.md` is the index.

## Building

Lean 4 v4.32.0 with Mathlib v4.32.0, and `ProveIt` required by path as a sibling
checkout:

```sh
# once: share ProveIt's package cache instead of re-downloading and rebuilding Mathlib
lake build          # both libraries
lake build Cardinals
lake build CoarseDegrees
```

Each library has an `Audit.lean` that prints, for its main theorems, the axioms they
depend on, so that the admitted published results are visible rather than buried.

## Status

Nothing here is refereed.  The reports are unrefereed continuations, the syntheses record
where they disagree and how far each argument was re-derived, and the Lean developments
state exactly what is admitted and on what authority.  Priority is not claimed for any
statement.
