<!-- SPDX-License-Identifier: MIT-0 -->

# Exacting and cover-exacting cardinals, and a collection of research reports

This directory holds a research project on large cardinals at the inconsistency
frontier — a research plan, a series of research reports, a deduplicated synthesis
and a Lean 4 formalization — together with a collection of research reports on
other subjects.

| | Subject | Lean library | Documents |
|---|---|---|---|
| **Large cardinals** | Exacting, ultraexacting and cover-exacting cardinals | `Cardinals/` | `docs/cardinals/` |
| **Other research reports** | Combinatorics, number theory, analysis and logic | none | `docs/reports/` |

The Lean library uses ProveIt's first-order syntax (`SetTheory.Form`, `Sat`) and its
internal-satisfaction machinery.  The coarse Turing degrees project, which uses the same
syntax layer, is in [`Computability/TuringDegrees/`](../../Computability/TuringDegrees/README.md).

## Large cardinals

Thirty-six research reports on cover-exacting, exacting and ultraexacting cardinals.
`docs/cardinals/research-synthesis/` combines them into one document, stating each result
once in the strongest form reached by any report, with a source tag and a concordance;
`docs/cardinals/research-notes/` holds a note on virtually exacting cardinals and large
countable ordinals.  `Cardinals/` formalizes the parts that are theorems of ZFC about a single
witness, admitting published results with citations; `Cardinals/README.md` has the
coverage table and the list of admitted statements.

The strongest result is that, in ZFC, a cover-exacting cardinal cannot lie between two
strongly compact cardinals — a partial negative answer to a problem of Blue and Goldberg.

## Other research reports

`docs/reports/` holds one hundred and four independent reports that are not formalized
here: ordinals and well-quasi-orders, Hankel determinants, supercongruences, tetration and digit stabilization, log-concavity,
graphs, automata and formal languages, enumerative combinatorics,
generating-function asymptotics, and quaternionic analysis.  Most attack a
specific conjecture from the literature or from an OEIS entry; about a quarter are
counterexamples rather than proofs.  Where several manuscripts proved the same
result, they are combined in one report that keeps each one's extra material and,
where the proofs genuinely differ, every proof.
`docs/reports/manifest.pdf` catalogues all one hundred and four, and `docs/reports/README.md` is the index.

## Building

Lean 4 v4.32.0 with Mathlib v4.32.0.  The package requires the ProveIt root by path
(`../..`).  Run from `SetTheory/Cardinals`, or from the ProveIt root with
`lake --dir SetTheory/Cardinals build`:

```sh
lake build          # the Cardinals library
lake env lean Cardinals/Audit.lean     # the axioms behind each main theorem
```

To avoid downloading and building Mathlib a second time, `.lake/packages` can be a
junction to the root workspace's `.lake/packages`.

**Admitted statements.** Unlike the rest of ProveIt, the `Cardinals` library closes nineteen
declarations with `admit`, all for results from the literature.  `Cardinals/Audit.lean`
prints, for the main theorems, the axioms they depend on, so that the admitted published
results appear as `sorryAx` rather than being buried; `Cardinals/README.md` lists them.

## Status

Nothing here is refereed.  The reports are unrefereed, the synthesis records
where they disagree and how far each argument was re-derived, and the Lean development
states exactly what is admitted and on what authority.  Priority is not claimed for any
statement.
