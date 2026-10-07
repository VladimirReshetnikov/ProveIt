# Source audit and attribution boundaries

Date of inspection: 6 October 2026.
Repository: VladimirReshetnikov/ProveIt.
Comparison snapshot: `869289aa38d59354e8dac2213df08ae0dd256415`.

The snapshot is the fixed commit used for the source reads, not a claim that
no later commit existed. The work was read through the GitHub connector;
no repository mutation was performed.

## Original paper

W. T. Gowers, *A new proof of Szemeredi's theorem*, Geometric and Functional
Analysis 11 (2001), 465–588.

The original proof of Lemma 16.10, particularly the sampling and interpolation
passage on printed pages 574–575, was inspected both as parsed text and in
PDF page images. The copy inspected was:

https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

The argument uses class-size truncation, samples with replacement, and then
interpolates from two supposed distinct hits. A two-hit binomial expression
does not in general certify two *distinct* elements. The inspected repository
already identifies this point and corrects it. This delivery does not claim
to discover that obstruction.

## Inspected implementation files

All paths below are under:
`Combinatorics/Ramsey/Lean/GowersSzemeredi/`

| File | Git blob SHA | What is used in the article |
|---|---|---|
| `Proofs16DistinctSampling.lean` | `365c13a69b45f9e9c23f05cdcda414ce53d6f156` | Exact repeated-sampling obstruction, split-class bound, sufficient budget `6*q <= r*sigma^2`. |
| `Proofs16AnchoredFibres.lean` | `cf6338c6bd7eee0939963958f7af4557cf0ce0ba` | Affine-cover anchored good-set theorem, long-column condition `2*q <= sigma*m`, loss at most `2*sigma`. |
| `Proofs16ShortColumns.lean` | `c6e268b0f39d098f872bc869e40841e82810f3f7` | Existing sampled-or-anchored interface, direct sampled lifts, short-column all-sample alternative, candidate cardinality. |
| `Proofs16RecoveredSliceCover.lean` | `3e2ebaba60f34dea95510e89971430b09b0041a5` | Existing common slice refinement: union-list bound `P <= Q(epsilon/(r*b),gamma,k)^(r*b)`, scale exponent linear in `r*b`, count `r*P+r^2*P^2`. |
| `Proofs16SynchronizedCover.lean` | `b0b9cae9bdea68a44ffa51e6a65079f03221f9a7` | Retiling under short-parent/unit-step/width conditions, without extra candidates or exceptional mass. |
| `Proofs16SynchronizedSliceCover.lean` | `4b7b30920f4bad1891578f21c688a637fcd6f4ef` | Assembled geometric hypotheses and `v^2+1 <= (m0/8)^(c(...)^(r*b))`. |
| `Proofs16ClosingComparison.lean` | `16c952e9c7329784de66e27a27079438994a97c4` | The wrong-direction same-dimensional closing inequality and an endpoint obstruction. |

Canonical URL pattern:

`https://github.com/VladimirReshetnikov/ProveIt/blob/869289aa38d59354e8dac2213df08ae0dd256415/Combinatorics/Ramsey/Lean/GowersSzemeredi/<filename>`

The source reads establish what is present in those files. This delivery did
not independently build that snapshot or re-run its Lean kernel checks.

## Attribution ledger

### Already in the paper/repository or standard background

- Affine interpolation from two distinct coordinates.
- The repeated-draw obstruction and a corrected distinct-anchor sampler.
- Direct sampled targets and the short-column all-sample case.
- A common horizontal-section refinement with scale exponent linear in the
  number of sampled sections.
- The distinction between a rectangular product and a proper common-step box.
- Synchronization without adding graph candidates, under its geometric input.
- The numerical closing-comparison obstruction.
- Occupancy/missing-mass methods, Lagrange interpolation, symmetrization,
  conditional expectation, and elementary symmetric mean inequalities.

### Proved in this manuscript and proposed for integration

- The exact fixed-subset, directly-sampled-target loss identity.
- A cutoff-free ambient-mass sampler with `O(q/sigma)` distinct anchors.
- Exact finite minimax realization by permutation-orbit row families.
- Exact hypergeometric finite differences, initial concavity, and the
  balanced-and-capped finite extremizer theorem.
- The explicit quadratic-radical cap for affine classes.
- Uniform finite-to-Poisson optimization, the two-regime loss curve, and the
  sharp sparse-sampling sample-size coefficient.
- Higher-degree/unisolvent-space and additive-corruption extensions of the
  shared-anchor mechanism.
- Label-preserving refinement and the elementary-symmetric candidate count.
- A parameter-explicit mathematical replacement at the existing
  sampled-or-anchored interface.

“Proved in this manuscript” is not a claim of historical priority. The
literature inspection was focused, not exhaustive, and the article is not
independently refereed.

## Related primary literature consulted

Daniel Berend and Aryeh Kontorovich, *The Missing Mass Problem*, arXiv:1111.2328
(2011). The source studies tight bounds on expected missing mass and extremal
distributions. Its role here is attribution and context, not a black-box
ingredient in the proofs.

https://arxiv.org/abs/1111.2328

Amichai Painsky, *Convergence Guarantees for the Good-Turing Estimator*, JMLR
23(279):1–37 (2022). The source explicitly treats occupancy probabilities for
symbols appearing a specified number of times. It provides context for
low-frequency occupancy quantities, not a theorem being claimed anew.

https://www.jmlr.org/papers/v23/21-1528.html

## Quantitative and logical boundaries

1. Minimax optimality is for the stated certification rule over arbitrary
   partial class partitions. It does not establish a lower bound for arbitrary
   polynomial algorithms, structured Gowers instances, or global Ramsey bounds.
2. The coefficient `t` is a simple finite upper bound. The Poisson coefficient
   `kappa_t` is asymptotically sharp under the stated sparse-sampling limits.
   The article does not interchange them without hypotheses.
3. The labelled refinement theorem is an abstract proved theorem whose
   restriction/scale hypotheses are explicit. The improved list count passes
   through source synchronization only when the needed geometric inputs are
   retained. No arbitrary-product-to-common-step-box claim is made.
4. The separate numerical closing gap of Lemma 16.10 remains open in this
   delivery. No complete global inverse/Szemeredi bound is announced.
5. Finite computation supports the proofs; it does not prove infinite or
   universally quantified statements by itself. No new Lean proof is supplied.
