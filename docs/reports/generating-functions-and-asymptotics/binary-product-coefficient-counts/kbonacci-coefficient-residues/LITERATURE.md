# Literature and status audit (finite-state route)

**One of two audits in this archive.** This file records the sources and the
bounded-search status for the *finite-state* proof of Conjectures 6.2 and 6.3
(canonical words, carry blocks, counter, parity automaton). The companion file
`RESEARCH_STATUS.md` records the sources and status for the *signed-cancellation*
proof of Conjecture 6.3 (coherent signings, flatness, overlap identity), which
cites Zhao, Diao, OEIS A104767 and Tang-Xin. Neither list contains the other;
the article's bibliography is their union, and both narratives are kept because
they record different things that were actually checked.

Audit date: September 20, 2026.

## Primary problem source

Richard P. Stanley, *Theorems and Conjectures on Some Rational Generating
Functions*, arXiv:2101.02131v3, last revised September 30, 2021.

- https://arxiv.org/abs/2101.02131v3
- https://arxiv.org/pdf/2101.02131

The relevant original pages were inspected as rendered PDF images as well
as parsed text:

- Printed page 17: k-bonacci initialization and the k >= 2 pair framework.
- Printed page 18: Lemma 5.2 and its equal-weight pair generators.
- Printed page 23: Conjecture 6.2, rationality of coefficient-residue counts.
- Printed page 24: Conjecture 6.3, the uniform odd-coefficient fraction,
  and the displayed modulo-three expressions for k=2 and k=3.

The manuscript gives a self-contained proof of the canonical-upper-row
factorization it uses. The general pair-generator shapes are not claimed
to be new. Likewise the two modulo-three rational expressions are taken
from Stanley, not presented as newly discovered formulas.

## Publication record

The paper appeared in European Journal of Combinatorics 119 (June 2024),
article 103814, DOI 10.1016/j.ejc.2023.103814.

- https://doi.org/10.1016/j.ejc.2023.103814
- https://www-math.mit.edu/~rstan/pubs/index.html (item 185)

Numbering in this manuscript follows the inspected arXiv v3, not an assumed
identity between arXiv and journal numbering.

## Related work checked

Shalosh B. Ekhad and Doron Zeilberger, *Automated Generation of Generating
Functions Related to Generalized Stern's Diatomic Arrays in the footsteps
of Richard Stanley*, arXiv:2103.12855v2 (October 20, 2024).

- https://arxiv.org/abs/2103.12855v2
- https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/stern.html

The companion page is marked last updated June 17, 2025. It describes
symbolic dynamic programming for generalized Stern arrays and includes
several moment and neighboring-coefficient computations. It also records
the solution of a different hard problem. That update does not by itself
resolve the coefficient-residue statements selected here.

## What the search does and does not establish

Targeted searches used the paper title and identifier, combinations of
Stanley/Fibonacci/coefficient/residue/rationality, and the exact conjecture
numbers. Several highly specific queries produced irrelevant results.
No later proof of the two target statements was identified in the results
inspected. This is a bounded search, NOT proof that the conjectures remained
open as of the audit date and NOT a guarantee of priority for this manuscript.

The correct status is therefore: an attempt at explicitly documented
conjectures, yielding complete proposed proofs and exact reproducibility
artifacts, with novelty and correctness still subject to independent review.
The manuscript does not claim to solve unrelated general C-finite sequence
questions, all of Stanley's conjectures, or the k=1 boundary case.

## Scope of this route within the merged archive

This route proves Conjecture 6.2 for every modulus and residue, and proves
Conjecture 6.3, but only for Stanley's initialization: its canonical normal
form and carry-block decomposition are derived from exactly the initial
segment w_0 = 1, w_i = (k-1)2^(i-1)+1 for 1 <= i < k. It does NOT prove the
seed-independent extension to arbitrary superincreasing seeds; that is the
separate contribution of the signed-cancellation route audited in
`RESEARCH_STATUS.md`. Conversely, that route does not reach moduli greater
than two. The merged article states both boundaries explicitly and does not
blur them.
