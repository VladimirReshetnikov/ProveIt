# Provenance, comparison scope, and mathematical status

Date of manuscript and source audit: 28 September 2026.

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `fbba58593dc0622aa914972896150d4848f935b5`.

Selected source directory:

`SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/shifted-catalan-hankel-polynomials/`

The report README and the relevant beginning and concluding portions of
`article.tex` were read through the connected GitHub interface. The larger
reports README and manifest were inspected to select a distinct research
extension. This was not a proof audit of every report in ProveIt.

The selected report proves the sharp quadratic-power recurrence for
`q=x^m(a+b*x)` and explicitly identifies multiple factors and collision
patterns as an extension. Its own status is unrefereed and not formalized.
The present article independently proves the mathematical foundations it uses
and recovers the prior recurrence as a special case.

## Primary literature consulted

1. Christian Krattenthaler, *Hankel determinants of linear combinations of
   moments of orthogonal polynomials, II*, arXiv:2101.04225v5 (10 September 2021),
   published in Ramanujan Journal 61 (2023), 597–627.
   https://arxiv.org/abs/2101.04225
   Theorem 1, Proposition 5, and Section 8 / Corollary 9 are the relevant
   comparison points. The PDF, including the recurrence statement and context,
   was inspected. This source supplies classical Christoffel/confluence theory
   and a general order-at-most-2^D recurrence, not a claim that 2^D is always
   minimal. Its discussion credits Elouafi's earlier Catalan recurrence proof.

2. Paul Barry, *Notes on the Hankel transform of linear combinations of
   consecutive pairs of Catalan numbers*, arXiv:2011.10827v1 (21 November 2020).
   https://arxiv.org/abs/2011.10827
   The introduction contains the denominator-exponent assertion discussed in
   the repository. The present article does not claim general rationality is
   new, and does not reproduce the separate coefficient conjecture without
   the repository's indexing qualification.

3. Johann Cigler and Christian Krattenthaler, *Hankel determinants of linear
   combinations of moments of orthogonal polynomials*, arXiv:2003.01676,
   International Journal of Number Theory 17 (2021), 341–369.
   https://arxiv.org/abs/2003.01676
   Used for the historical context and related determinant program; the
   present universal proof does not import an unverified specialized claim
   from this paper.

4. Christian Krattenthaler, *A determinant identity for moments of orthogonal
   polynomials that implies Uvarov's formula for the orthogonal polynomials
   of rationally related densities*, arXiv:2103.03969.
   https://arxiv.org/abs/2103.03969
   A starting reference for the rational-multiplier research question, not an
   input to the main proofs.

## Novelty scope

General polynomial-multiplier rationality and the Christoffel formula are
classical and are not presented as new. The proposed extension is the exact
branch degree `binom(m,2)+binom(ell+1,2)+sum k_i(t_i-k_i)`, the explicit
nonvanishing leading constant, the resulting minimality classification off
resonance, and their assembled structural and algorithmic consequences.
The secondary-Hankel identity for an arbitrary exponential polynomial is an
elementary confluent-Vandermonde calculation; novelty is not claimed for that
standalone linear-algebra identity.

Targeted searches combined Catalan Hankel determinants, repeated roots,
multiplicity, minimal recurrences and the degree expression. Some searches
returned little relevant material or unrelated results. They do NOT establish
that the theorem has never appeared in another notation. In particular,
Schur-function, Toeplitz/Hankel determinant, and orthogonal-polynomial
literature may contain equivalent specializations. Independent expert review
and a broader priority search would be needed before a first-discovery claim.

The eight proposed future directions are research tasks relative to this
article. They are not all represented as globally open problems in published
literature.

## Proof and computational status

The general theorems are proved in ordinary mathematics in `article.tex`.
No Lean or other proof-assistant verification was run. No global current
open-problem status is asserted based only on a source calling something
conjectural in an earlier version.

The verification suite ran successfully using exact rational arithmetic and
recorded 2,843 checks. This is finite supporting evidence. For particular
specializations, the article separately proves why a sufficiently long finite
certificate is conclusive AFTER an all-index recurrence bound is established.
The central-root fourth-power example is presented in exactly this way.

All proofs avoid division by the weighted determinants H_N themselves; signed,
zero and resonant minors are permitted. The theorem is over characteristic
zero and should not be transported unchanged to small positive characteristic.
Asymptotic results have fixed parameters; uniform collision limits are posed
as further research, not silently assumed.
