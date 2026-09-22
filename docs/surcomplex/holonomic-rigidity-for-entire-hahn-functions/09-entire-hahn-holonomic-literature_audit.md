# Targeted literature and repository audit

Date: September 22, 2026.

## Repository evidence

Inspected through the GitHub connector, not a stale public README snapshot:

- Repository: VladimirReshetnikov/Surreal.
- Pinned commit: a3124af79f66b8b9c196d76b4cbc5ac3938907c4.
- Recursive repository tree and docs directory.
- Relevant ranges of docs/manifest.tex, including the entire-function,
  differential-equation, rank-one analytic, dynamics, and spectral entries.
- Full README of docs/surcomplex/entire-functions-at-arbitrary-rank/.
- A repository content search for `holonomic` returned no matches.

The existing entire-function report explicitly distinguishes order units
from countable cofinality and already discusses the group
Gamma_infinity = direct_sum Q*omega^n. Those ideas and that workspace are
not claimed as new here. The new target is the exact classification for a
prescribed dilation q. The ordinary derivative is not the scalar derivation
used by the differential-equations package. The familiar quadratic-exponent
entire example already occurs in the repository and is not claimed as new.

A negative keyword search is not proof of absence. The audit does not claim
a line-by-line inspection of every source file in the repository.

## Primary literature inspected

1. R. P. Stanley, Differentiably Finite Power Series (1980), pp. 175-188.
   https://math.mit.edu/~rstan/pubs/pubfiles/45.pdf
   The first two pages were inspected as images: definition, linear equation
   formulation, and Theorem 1.5 connecting D-finite and P-recursive objects.
   This equivalence is classical and explicitly credited.

2. S. Garoufalidis, The degree of a q-holonomic sequence is a quadratic
   quasi-polynomial, arXiv:1005.4580v4 (2011 manuscript).
   https://arxiv.org/abs/1005.4580
   https://people.mpim-bonn.mpg.de/stavros/publications/degqholonomic.pdf
   Inspected the definition of q-holonomic sequences with variable q,
   Theorem 1.1, its Puiseux/rational-function setting, and Remark 1.2.
   The relevant theorem page was also inspected as an image.
   This is an important antecedent, not a result superseded or rediscovered
   under an unqualified novelty claim.

3. L. Di Vizio, An ultrametric version of the Maillet-Malgrange theorem
   for nonlinear q-difference equations, arXiv:0709.2464v2; Proc. AMS
   136(8) (2008), 2803-2814.
   https://arxiv.org/html/0709.2464v2
   Inspected the abstract, introduction, nonlinear Gevrey statements and
   the discussion of |q|=1. This provides related ultrametric theory, not
   an inspected proof of the arbitrary-rank order-unit classification.
   No nonlinear generalization of Di Vizio's theorem is claimed.

4. G. E. Andrews and S. O. Warnaar, The product of partial theta functions.
   https://people.smp.uq.edu.au/OleWarnaar/pubs/Partial-thetas.pdf
   The first page was inspected as an image and identifies the standard
   partial-theta series used here (up to a sign convention). The series
   and its elementary functional identity are not original contributions.

5. G. Higman, Ordering by Divisibility in Abstract Algebras (1952).
   https://doi.org/10.1112/plms/s3-2.1.326
   Publisher metadata checked. The finite-word theorem is used as a
   standard external ingredient for the positive-support monoid lemma.

6. E. Kaplan, L. S. Krapp, M. Serra, Decomposing the automorphism group of
   the surreal numbers, arXiv:2509.22374v3.
   https://arxiv.org/html/2509.22374v3
   Inspected the Hahn-field conventions and the Conway-normal-form
   identification with t = omega^(-1). Authors and version verified.
   No automorphism theorem from this paper is a dependency of our new
   classification.

## Search limitations and priority statement

Targeted searches covered Hahn fields and D-finiteness, Hahn fields and
q-difference equations, ultrametric q-difference equations, q-holonomic
valuation/degree growth, partial theta functions, and the named primary
sources above. Some broad keyword queries produced irrelevant results and
were not treated as evidence of absence.

The main proposed contribution is the iff classification for a fixed
nontorsion Hahn parameter at arbitrary valuation rank, together with its
quantitative support-exclusion formulation and universal no-order-unit
corollary. We did not locate this exact statement in the inspected sources.
This is not certification of publication priority, an exhaustive database
search, independent peer review, or a claimed solution of a named published
open problem. The article's proofs, rather than a search failure, support
the mathematical claims.
