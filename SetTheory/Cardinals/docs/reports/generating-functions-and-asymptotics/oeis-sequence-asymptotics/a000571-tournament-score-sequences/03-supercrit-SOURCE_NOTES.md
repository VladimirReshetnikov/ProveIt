# Source and provenance notes

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Continued report:
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000571-tournament-score-sequences/`

The report's README and the opening/source portions of its LaTeX manuscript were read through the GitHub connector. The relevant scope statement was re-read at this explicit commit:

`106eb191a2a47ab6281e2c26c7f4fe3d28872b83`

Pinned scope source:
https://github.com/VladimirReshetnikov/ProveIt/blob/106eb191a2a47ab6281e2c26c7f4fe3d28872b83/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000571-tournament-score-sequences/README.md

Lines 120–170 explicitly exclude the supercritical moving-pole regime and identify its unresolved crossover as Part I question 2 / Part II RQ6. The pinned README blob SHA returned by the connector was `63322ccbce51ab921ca516521963c8fe852c4de5`.

The pin is a **commit** SHA. The earlier exploratory response from `git/trees/main` returned `db20eb37982abc0f163c6d308d392f5ac4c9bc62`; that was a tree SHA and is not used as a commit pin. The branch changed during research; no claim is made that the initial exploratory tree and final pin are identical. The relevant open-question statement was checked explicitly at the final pin.

The pin's UTC timestamp is 5 October 2026; the local Pacific date was 4 October. The manuscript uses the latter date. This package is newly generated; no repository file was modified or uploaded.

## OEIS and primary literature

- https://oeis.org/A000571 — all score sequences, exact recurrence and initial terms. This is not the sequence of labeled tournaments.
- https://oeis.org/A351822 — strong score sequences. Its empty object is not a strong block in `I(z)` here.
- https://oeis.org/A145855 — auxiliary divisor formula, with the Alekseyev attribution.
- https://arxiv.org/abs/2209.03925 — Claesson, Dukes, Franklín, Stefánsson, *Counting tournament score sequences*. The primary PDF pages on the exact identity and block decomposition were also inspected. The CDFS identity is the one nontrivial exact-enumeration input credited without re-proving its bijection.
- https://arxiv.org/abs/2209.13563 — Kolesnik, *The asymptotic number of score sequences*, Combinatorica 43 (2023), 827–844. The leading all/strong asymptotics and the unweighted component law are prior work.
- https://arxiv.org/abs/2407.01441 — Bassan, Donderwinkel, Kolesnik, *Tournament score sequences, Erdős–Ginzburg–Ziv numbers, and the Lévy–Khintchine method*. ECP 31 (2026), DOI 10.1214/26-ECP751.
- https://arxiv.org/abs/1109.1028 — Grabchak, *On a new class of tempered stable distributions: moments and regular variation*. Cited to place the use of tempered stable laws in established theory; our limiting characteristic exponent is derived directly.

Entries and papers were accessed during this session on 4 October 2026 Pacific time. The numerical constants printed in the article are computed from the exact generating function, rather than copied from an entry.

## Limits of the search and of the claims

This was a bounded search of the listed sources and the repository, not an exhaustive review of MathSciNet, zbMATH, journal archives, or all generalized renewal literature. “New” means a proved development relative to the inspected report; no publication-priority certificate is asserted. The article rederives its local analytic input rather than assuming an unrefereed repository asymptotic theorem.

The work is AI-assisted, unrefereed, and not Lean- or Rocq-formalized. Exact symbolic/finite-integer checks are distinguished from numerical diagnostics and from conventional analytic proofs. Floating-point output is not outward-rounded. The README and article list the major unresolved extensions.
