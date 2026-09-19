<!-- SPDX-License-Identifier: MIT-0 -->

# Research reports

Sixty-four independent mathematical research packages, unpacked from the
archives in which they were delivered and grouped by subject.  Each directory
holds a typeset article with its LaTeX source, a `README.md`, and in most cases
verification code together with the recorded output of running it.

**[`manifest.pdf`](manifest.pdf)** ([source](manifest.tex)) is the catalogue: it
numbers all sixty-four reports, names the problem each one attacks and the
result it claims, and records the archive each directory came from.  These are
AI-assisted drafts; none is refereed or machine-checked, and the manifest
records what each report claims rather than verifying it.

| Category | Reports |
|---|---:|
| [`ordinals-and-order-types/`](ordinals-and-order-types) — friendly order types, wqo powersets and statures, transfinite words, ordinal arithmetic, games | 15 |
| [`hankel-determinants/`](hankel-determinants) — Somos and elliptic, Catalan and ballot, arithmetic Hankel, growth and runs | 9 |
| [`congruences-and-valuations/`](congruences-and-valuations) — supercongruences, iterated series, valuations and periodicity | 8 |
| [`tetration-and-digit-stabilization/`](tetration-and-digit-stabilization) — congruence speed, frozen digits, `q`-Newton series | 7 |
| [`log-concavity-and-unimodality/`](log-concavity-and-unimodality) — cluster variables, chromatic coefficients, Stirling rows, independence systems | 7 |
| [`graph-theory/`](graph-theory) — mutual visibility, domination roots, minimal dominating sets | 3 |
| [`enumerative-combinatorics/`](enumerative-combinatorics) — parking functions, pattern avoidance, Hardinian arrays, preorder polytopes | 8 |
| [`generating-functions-and-asymptotics/`](generating-functions-and-asymptotics) — Stanley's rationality question, Gregory thresholds, records, discrepancy | 7 |
| **Total** | **64** |

## Rebuilding the manifest

```sh
latexmk -pdf manifest.tex && latexmk -c manifest.tex
```

## A note on directory names

Several of these reports attack the same published problem, and some arrived
under colliding archive names, so each directory is named for its own angle on
the problem rather than for the archive it came from.  The manifest records the
original archive name with every entry.
