# Source audit and novelty boundary

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned snapshot: `3d5973524506411392a911470b5ddc35521568ea`.
Selected repository sources were retrieved using the connected GitHub tools.
No repository write was made.

### Linear Hahn–Fuchsian package

Path:
`Analysis/Transseries/docs/series-and-transseries/Hahn_Fuchsian_Resonance_Analytic_Normalization/`

The README was read, and selected contiguous sections of `hahn_fuchsian.tex`
were inspected: the introduction and framework, lines 1020–1240
(accumulation example and crossover), 1280–1440 (verification and research
questions), and 1440–1505 (further questions and conclusion).
The TeX blob reported by GitHub was
`232332c2a998f7768ad20359fadc67deae260f4b`.

That work treats linear matrix-gauge normalization and spectral DIFFERENCES.
It already provides finite resonance data and a sharp universal gap criterion.
The present article does not claim these as new. Its unknown is a nonlinear
solution with resonant parameters; the main additional classification concerns
the algebraic locus of absolute convergence for a fixed equation, even with
zero gap. The new solution problem uses eigenvalues of A rather than the
spectral differences of a gauge operator.

### Support formalization

Path:
`Algebra/SurrealNumbers/Surreal/HahnSeries/NeumannWords.lean`

Lines 1–130 were inspected at the pinned snapshot. Reported blob:
`b7b0943c6784b2dfa9015c07bdbd188cacc799c2`.

The inspected source includes `isPWO_closure_of_pos`, `finite_wordsWithSum`,
and `finite_multisetsWithSum`, with a general ordered-monoid support proof.
It does not require an Archimedean hypothesis for exact-word finiteness.
Our real lower bound is used for a uniform degree estimate, not as a claim
that general ordered-group word finiteness fails. This Lean file was not
recompiled in the present work.

Repository searches also checked Fuchsian, small-divisor, Neumann, Briot,
and convergence-locus terminology. Search coverage is not a proof of absence
of another equivalent result. The large canonical volume and the full
repository were NOT audited line by line.

## Primary literature

1. J. van der Hoeven, *Operators on generalized power series*, Illinois Journal
   of Mathematics 45 (2001), 1161–1190.
   DOI: https://doi.org/10.1215/ijm/1258138061
   Author version: https://www.texmacs.org/joris/noeth/noeth.html
   Used to acknowledge prior generalized-series operator and implicit-function
   methods. No general fixed-point theorem is claimed as a new discovery.

2. R. R. Gontsov and I. V. Goryuchkina, *On the convergence of generalized
   power series satisfying an algebraic ODE*, Asymptotic Analysis 93 (2015),
   311–325.
   DOI: https://doi.org/10.3233/ASY-151297
   Preprint: https://arxiv.org/abs/1407.1330
   Its complex-exponent generalized-series setting with real parts tending
   to infinity was checked. The present finite-accumulation coefficient
   setting is not identified with an ordinary analytic coefficient germ
   at x=0. The opened PDF supplied parsed text; a screenshot request failed
   with a cache error. No claim here depends on a figure or image in it.

3. R. Gontsov and I. Goryuchkina, *Convergence of (generalized) power series
   solutions of functional equations*, arXiv:2412.00778 (2024).
   https://arxiv.org/abs/2412.00778
   English extended abstract: https://arxiv.org/html/2412.00778v1
   The stated convergence and finite-generation framework was inspected.
   This article is cited as prior theory rather than as an equivalent
   statement of the zero-gap parameter-locus theorem.

4. M. Joswig and B. Smith, *Convergent Hahn series and tropical geometry of
   higher rank*, Journal of the London Mathematical Society 107 (2023),
   1450–1481.
   DOI: https://doi.org/10.1112/jlms.12716
   Used to acknowledge established absolute Hahn-convergence notions.

## Claim of contribution

The proposed contribution is the combination of a bounded dangerous-exponent
window, algebraicity of the resonant-parameter convergence locus at zero gap,
a sharp weighted-degree bound, common radii on compact parameter sets, and
universality realizing arbitrary affine algebraic loci without formal
compatibility obstructions. Explicit auxiliary results and examples support
that main theorem.

The literature comparison is targeted, not exhaustive. The package supplies
proofs of its statements but does not certify historical priority, a resolution
of a famous general conjecture, independent peer review, or Lean verification.
