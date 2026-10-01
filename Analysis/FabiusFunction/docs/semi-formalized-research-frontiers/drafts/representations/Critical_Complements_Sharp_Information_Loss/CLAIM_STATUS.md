# Claim and verification status

## Proved in the manuscript

Theorem 2.1 (fixed complement): explicit phase constants for overlap and
relative entropy, the exact compact boundary-deficit correction, its
O(n^-3/2 (log n)^3) overlap remainder, and the 1/n entropy coefficient with
O(n^-2) remainder. All parameters q, rho, and m are fixed in this theorem.

Theorem 2.2 (sublinear complement): the sequentially uniform leading
equivalent for every 1 <= m=o(n), including the three overlap regimes and
the Lambert-W crossover. The m=0 case is included in the thin-complement
law. This leading equivalent must not be expanded into a second-order
fixed-m assertion.

Theorem 2.3: D = (1/2)log(n/m) - 1/2 + o(1) when m grows and m=o(n);
the full-configuration entropy asymptotic; and the exponential-noise
mutual-information interpretation of the fixed-complement entropy gap.

Supporting results: exact likelihood and Fabius-CDF profile; signed Gamma
convolution identities; central and saddle density estimates; phase
derivative and reindexing identities; and complement entropy monotonicity.

## Imported background

Convolution preservation of log-concavity is attributed to Prékopa.
Stirling's formula, Gamma densities, exponential tilting, and elementary
entropy identities are classical. Classical Gibbs-conditioning context
is attributed to Diaconis–Freedman and Dembo–Zeitouni. Those conditional
limit theorems are not used as unverified uniform estimates in our proofs.

## Computational status

The delivered Python run passed its recorded numerical checks. These use
ordinary floating point and are not interval-certified. No theorem is
established merely by the numerical output. No Monte Carlo is used.

## Limits

The main scope fixes q and the tilt phase, uses inequality conditioning at
the tilted mean, and observes a prefix. The general-weight and arbitrary-mask
critical-complement problem remains outside the proved scope. The exact
boundary deficit has not been expanded into a fully explicit endpoint
transseries. Entropy monotonicity in rho has not been proved.

This is not a Lean/Rocq formalization or an externally refereed paper.
The repository inspection and literature check are targeted, not exhaustive.
Worldwide novelty and research priority are not certified. No named famous
conjecture is claimed to have been settled.
