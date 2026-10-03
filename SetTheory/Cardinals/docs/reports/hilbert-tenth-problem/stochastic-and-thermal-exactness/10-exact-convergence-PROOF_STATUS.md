# Proof, novelty, and implementation status

Date: October 2, 2026.

## Results proved in the manuscript

The proof development provides an effective counter-machine-to-game compiler,
including a normalized paired-channel construction, a fully initialized cyclic
pipeline, a proof covering every intermediate iteration, and an erasing-halt
convention that drains all internal state. A common uniform reset preserves
exact comparisons, and a uniform reward centers the computation at an obvious
fixed point. These steps prove the constrained fixed-game c.e.-completeness
result stated as Theorem 1.1, as well as its scalar and consensus variants.

A separate direct arithmetic compiler gives a single orthant-nonnegative
quadratic for each fixed horizon, with a unique complete natural witness when
the endpoint predicate holds. Complete example polynomials are exported,
not merely formulas that call an unspecified execution relation.

The counter source model's universality is an established external ingredient.
The fixed universal game is an effective existence result obtained by compiling
a fixed universal counter program, not a shipped numerical universal table.

## Attribution and what is not new

The MRDP equivalence, ordinary stochastic-game contraction facts, and
universality of suitable counter machines are established results.
The repository already has strict-contraction and quadratic neural-certificate
work. Skolem-equivalence for ergodic Markov-chain observations is known from
Vahanwala's paper; the manuscript gives a compatible dyadic reset construction,
not a claim to have discovered the underlying phenomenon.

The original development claimed here is the explicit combination of native
stochastic-game restrictions, the erasing exact-convergence reduction, and its
complete bounded arithmetic interface. A targeted source search did not
establish publication priority for the precise theorem. Mathematical validity
and novelty must be evaluated independently.

The close one-player comparison uses Varonka and Watanabe, arXiv:2502.19923v3,
January 26, 2026. The new construction requires both MIN and MAX owners and
mixed-sign centered initializations. It does not resolve their remaining
one-player cases. The general Skolem discussion includes the July 2026
conditional-decidability paper, arXiv:2607.15510.

## Checks performed

The delivered suite passes 26,077 exact arithmetic assertions with seed
20261002. These include local quadratic equivalences, circuit successor
correctness on finite test inputs, normalization and layering, every tested
microstep, the reset identity, edge cases with initial halting, full fixed-point
attainment, expanded/factored polynomial agreement, exact resource ledgers,
and independently checked exported polynomial zeros and trajectories.

The two-state example is fully expanded. The larger certificate files give all
integer coefficients in a sum-of-squared-linear-forms-plus-products format.
The independent checker imports no generator code. The full list of tests,
including their counts and exact scope, appears in artifacts/verification.json.
Unit-coordinate mutation checks on the 2,584-witness example use exact
coefficient-based polynomial differences; they are not full dense
re-evaluations for every coordinate. The article records this distinction.

No theorem in this archive has been checked in Lean, Rocq, or another proof
assistant. The repository's MRDP interface was read, not rebuilt. No empirical
test is presented as a proof of an infinite or universal assertion.

## Claims expressly not made

This work does not compute a small numerical universal game, prove an
unrestricted arithmetic-circuit optimum, improve the 87-operation bound
reported by the inspected repository README, solve general Skolem, settle
single-fold/finite-fold MRDP, or turn the horizon-indexed quadratic family into
a fixed-arity quadratic representation of a c.e.-complete set.

The fixed-arity polynomial and quartic consequences in the article use MRDP.
An explicit universal polynomial is not exported. Unique bounded-run witnesses
do not transfer to arbitrary MRDP witnesses without another theorem.
