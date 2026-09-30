# Sources and provenance

Research date: September 29, 2026 (America/Los_Angeles).

## Inspected repository

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Commit: `1ee53d57de253d16cdaad79d1f54bbd95d76d682`
- Root tree recorded by that commit: `c772efcde0cc2db7902005598190606da6cb338c`
- Commit endpoint used to confirm the pin:
  https://api.github.com/repos/VladimirReshetnikov/ProveIt/commits/1ee53d57de253d16cdaad79d1f54bbd95d76d682
- Relevant directory:
  `SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/`
- Pinned README:
  https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/1ee53d57de253d16cdaad79d1f54bbd95d76d682/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/README.md

The README records a three-part merged report. Part III is the September 29
manuscript *The Largest Jump Is Almost Maximal: An algebraic boundary law for
random 132-avoiding permutations*, incorporated with the prefix
`03-largest-jump-`. It occupies Sections 21–36 of the combined report.
The relevant proposed questions are Sections 32.1 (bulk scaling) and 32.2
(exact leading moments). The README explicitly says these are not proved there.

For the detailed earlier proofs and questions, the original standalone
LaTeX source `article(20260929-161704).tex` was read from the user's Library,
including the finite stopping construction and the open-question section.
This source corresponds to the earlier *Largest Jump* article. Its own
reference pin is `8d936ee2357f9decf78c2ecc7d9baf3100a6787d`; that is not the
pin of the present article.

The current proof credits and rederives the stopping-word construction.
The earlier algebraic boundary law and its asymptotics are contextual, not
assumptions used to establish the new theorems. No earlier manuscript or
external PDF is redistributed in this package.

## Primary external literature checked

1. Nathaniel Nadler, *On 132-Avoiding Permutations with an Adjacency Constraint*,
   arXiv:2604.22135v1, submitted April 24, 2026.
   https://arxiv.org/abs/2604.22135
   Used for the problem's fixed-bound context and attribution.

2. Teruki Mayama and Dai Akita, *Finite-state enumeration of
   adjacency-constrained 132-avoiding permutations*, arXiv:2605.23519v1,
   submitted May 22, 2026.
   https://arxiv.org/abs/2605.23519
   https://arxiv.org/html/2605.23519v1
   Used for finite-state context, endpoint-state methods, and the distinction
   between fixed-bound spectral questions and the proportional-bound regime.

The accessible records were rechecked during this task. The article does
not transfer a theorem about fixed m to the regime m proportional to n.
The necessary finite Catalan identities and probability estimates are proved
in the article itself.

## Literature-scope limitation

Targeted searches concerned largest adjacent differences in 132-avoiding
permutations and the associated bulk limit. They did not establish a
matching macroscopic formula from the retrieved material. This is not an
exhaustive literature review or a priority certification. No claim that a
classical named open problem has been resolved is made; the identified
questions are explicit open directions in the inspected ProveIt report.

## Proof and computation boundary

- Written proof: all-n finite lemmas, convergence of the marked measure,
  bulk profile, moments, biased limits, and constructive lower bounds.
- Exact regression tests: finite integers and rational identities over the
  stated ranges, separately recorded in `data/verification.json`.
- Numerical illustrations: Monte Carlo output, not a proof, rigorous
  interval enclosure, or fitted asymptotic theorem.
- Formal proof assistants: no Lean/Rocq implementation or verification claimed.

No remote repository was edited and no pull request or commit was created.
