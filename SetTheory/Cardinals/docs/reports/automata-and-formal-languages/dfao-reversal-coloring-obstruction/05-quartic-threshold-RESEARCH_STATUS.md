# Research status

## Proved in the article by conventional arguments

1. Strict balancing of complete bipartite coloring counts for k>=3.
2. Explicit nearest-coprime optimization of the Davies lower expression for
   every k>=4,n>=7 with k<n; no asymptotic hypothesis for this optimization.
3. The universal upper bound matching that expression for every k>=4 and
   n>=N(k), with N(k)<=3k^4.
4. Exactness in that range, using the published lower construction.
5. Necessary extremizer cycle structure, proper full-period output coloring,
   complete improper-coloring coverage, and singular-letter rank n-1.
6. The matching obstruction hierarchy for arbitrary two coprime cycle sizes
   and singular kernels consisting of cross pairs, with no large-n condition.
7. An exact first matching correction and a quantitative one-cross-edge loss.
8. Even/odd exponential asymptotics for the optimal deficit.

## Computer-assisted extensions

The finite inequalities below N(k) are checked for k=4,5,6,7 by two implementations.
Their strict exclusions extend both the exact optimum and the necessary
structural rigidity to every n>=max(7,k+1) in these four slices.

Each implementation performs 9,247,046 comparisons in 2,217 rows. These are
finite structural comparisons, not counts of enumerated automata. The
independent implementation uses a stronger residual-order comparison; all
its excluded mixed cases pass even the first coarse integer test.

The third program contains supplementary finite tests, not a third independent
implementation of the full proof. It imports the primary chromatic routine
when comparing that formula to an independently written positive formula.

## Imported results and established antecedents

The lower witness is imported from Davies, arXiv:1705.07150v2. The coloring
orbit reduction is known there and is reproved in the manuscript. The
collision-orbit approach is an established part of the inspected ProveIt
report. The repository already contains a complete three-output investigation.
This article's target is the four-and-more-output frontier.

No novel-invention claim is attached to standard Stirling recurrences,
Rolle's theorem, graph coloring, the Chinese remainder criterion, or the
published lower monoids.

## Not established

- The full formula for all k>=8 and max(7,k+1)<=n<N(k).
- The k=n boundary.
- Small n outside the stated ranges.
- A sufficient classification of singular transitions attaining the optimum.
- The second-best attainable value or the entire near-optimal spectrum.
- Uniform asymptotic error terms for arbitrary growing k; the main threshold
  is uniform, but the displayed asymptotic expansions are fixed-k statements.
- Historical priority beyond the inspected sources.
- Independent refereeing or proof-assistant certification.

The mathematical arguments are research claims open to external scrutiny.
The finite computations and the published dependency are separated from the
self-contained upper-bound proofs so that each trust boundary is visible.
