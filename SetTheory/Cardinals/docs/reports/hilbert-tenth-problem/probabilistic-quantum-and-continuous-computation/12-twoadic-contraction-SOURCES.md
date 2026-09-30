# Sources and provenance

Inspected September 30, 2026.

## ProveIt snapshot

Commit: `b6bf6406a4c49017fedc6fba068b36c634987150`.

The repository was read through the GitHub connector. Relevant full files:

1. `Computability/HilbertTenthProblem/README.md`
   https://github.com/VladimirReshetnikov/ProveIt/blob/b6bf6406a4c49017fedc6fba068b36c634987150/Computability/HilbertTenthProblem/README.md
2. `Computability/HilbertTenthProblem/Lean/MRDP.md`
   https://github.com/VladimirReshetnikov/ProveIt/blob/b6bf6406a4c49017fedc6fba068b36c634987150/Computability/HilbertTenthProblem/Lean/MRDP.md
3. `Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`
   https://github.com/VladimirReshetnikov/ProveIt/blob/b6bf6406a4c49017fedc6fba068b36c634987150/Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean

The guide and theorem provide fixed finite natural-witness MRDP, including
input zero, and the converse. The guide explicitly does not promise a
practical coefficient-generating algorithm or a numerical witness bound.
Its statements about prior Lean builds and axiom audits were not independently
rerun here. Search-index results were not treated as replacing this pinned
source version.

## Primary literature consulted

- Vladimir Anashin, *Automata finiteness criterion in terms of van der Put
  series of automata functions*, arXiv:1112.5089 (2011), published in
  p-Adic Numbers, Ultrametric Analysis and Applications 4 (2012), 151–160.
  https://arxiv.org/abs/1112.5089
  DOI: 10.1134/S2070046612020070.
  Relevance: the Lipschitz/transducer interface and the separate issue of
  finite-state realizability.

- Jean-Charles Delvenne, Petr Kůrka, Vincent Blondel, *Decidability and
  Universality in Symbolic Dynamical Systems*, author version headed
  Fundamenta Informaticae 74 (2006), 1–28.
  https://www.cts.cuni.cz/~kurka/decid1.pdf
  Relevance: clopen observation; Section 7.4, Proposition 19 and Corollary 20
  give the equicontinuity obstruction. The title page and relevant theorem
  page were inspected as rendered PDF pages as well as parsed text.

- Cristopher Moore, *Unpredictability and undecidability in dynamical
  systems*, Physical Review Letters 64 (1990), 2354–2357.
  https://doi.org/10.1103/PhysRevLett.64.2354
  Relevance: historical context for dynamical simulation of computation.
  The publisher's abstract and bibliographic record were consulted; the
  present proofs do not depend on the unavailable full publisher text.

- Mario Carneiro, *A Lean formalization of Matiyasevič's Theorem*,
  arXiv:1802.01795 (2018).
  https://arxiv.org/abs/1802.01795
  Relevance: the formalization of Diophantine exponentiation. It is not cited
  as a claim that this 2018 paper formalizes the entirety of MRDP.

## Novelty-search limitation

The sources above establish the immediate conceptual context, not priority
for the exact construction or each structural theorem. Broader searches on
contracting transducers, 2-adic halting, and exact extinction did not yield a
reliable exhaustive comparison. In particular, irrelevant general search
results are not evidence that related mathematical literature is absent.

The article therefore proves its own precisely stated results without
claiming verified first publication, a historically recognized open-problem
solution, or independent confirmation of a breakthrough. A publication-ready
priority assessment should extend to iterated transducers, symbolic-system
simulation, and regularity-restricted termination problems.
