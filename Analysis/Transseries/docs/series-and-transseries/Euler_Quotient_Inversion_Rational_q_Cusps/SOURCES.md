# Sources and inspection boundary

Research date: 4 October 2026.

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Tree snapshot: `8e9cd6f00e0ac79c4425ff6abdfa64b497cf3f41`.
The repository was inspected through the GitHub connector. The targeted
comparison used the following documentation:

1. `Analysis/Transseries/README.md`.
2. `Analysis/Transseries/docs/series-and-transseries/README.md`.
3. `Analysis/Transseries/docs/series-and-transseries/Certified_Inversion_q_to_1_Transition/README.md`.
4. `Analysis/Transseries/docs/series-and-transseries/Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/README.md`.

The sibling READMEs include their editorial scope and overlap qualifications.
The comparison does not purport to read or audit every proof in the canonical
volume, all of its full TeX sources, or every incoming research package.
No results are claimed to be absent from the entire repository on the basis
of a title search. No repository files were modified.

## Primary literature

The bibliography in article.tex contains the complete references. The
following roles explain the principal dependencies:

- David Sauzin, *Nonlinear analysis with resurgent functions*, Ann. Sci. ENS
  48 (2015), 667–702. https://doi.org/10.24033/asens.2255
  https://arxiv.org/abs/1212.4477
  Established nonlinear resurgent operations and inversion; not an open
  theorem claimed to be solved by this article.

- NIST DLMF §27.14, https://dlmf.nist.gov/27.14
  Classical eta product and modular transformation. The article re-derives
  all local Euler-quotient constants and phases from that transformation.

- NIST DLMF §17.2, https://dlmf.nist.gov/17.2
  Standard finite q-binomial notation and identities.

- Richard J. McIntosh, *Some asymptotic formulae for q-shifted factorials*,
  Ramanujan J. 3 (1999), 205–214.
  https://doi.org/10.1023/A:1006949508631
  Classical all-order q-factorial expansion context. The needed special case
  is proved directly in the article rather than relying on an unseen theorem.

- Stavros Garoufalidis and Don Zagier, with an appendix by Sander Zwegers,
  *Asymptotics of Nahm sums at roots of unity*, Ramanujan J. 55 (2021), 219–238.
  https://doi.org/10.1007/s11139-020-00266-x
  https://arxiv.org/abs/1812.07690
  Root-of-unity asymptotic background and a route for future multi-saddle work.

- Veronica Fantini and Claudia Rella, *Modular resurgence, q-Pochhammer
  symbols, and quantum operators from mirror curves*, Letters in Mathematical
  Physics 116 (2026), no. 2, article 39.
  https://doi.org/10.1007/s11005-026-02063-x
  Preprint arXiv:2506.08265 (2025; revised 1 April 2026).
  https://arxiv.org/abs/2506.08265
  Resurgent and summability context; the article does not claim to resolve
  the full set of questions studied in that work.

- Arash Arabi Ardehali and Hjalmar Rosengren, *A New Product Formula for
  (z;q)_infinity, with Applications to Asymptotics*, Constructive Approximation
  (2026), version of record published 19 September 2026.
  https://doi.org/10.1007/s00365-026-09783-2
  https://arxiv.org/abs/2602.11329
  Current nonmodular q-product and gamma-product asymptotic context. The
  article does not claim a new product formula for general shifted factorials.

## New derivations and evidence

The proposed contribution is the explicit branch-aware synthesis, the
three-invariant inverse classification, the intrinsic correction-ramification
criterion and four-factor realizations, and the divisor-cusp inverse-data
reconstruction formula. Conventional proofs and source boundaries are in the
article. Global priority is not certified.

Exact arithmetic tests and high-precision numerical diagnostics are stored
separately. They do not replace the proofs and are not interval certificates.
