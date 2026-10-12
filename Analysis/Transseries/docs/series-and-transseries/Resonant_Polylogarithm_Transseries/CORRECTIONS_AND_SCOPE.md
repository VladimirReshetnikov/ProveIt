# Corrections, safeguards, and limits

## What was and was not found

No new error was established in the accepted repository theorem statements
actually inspected. The source audit is deliberately bounded. Existing
editorial corrections and the accepted/pending distinction are respected.
The historical bridge article's statements are not silently promoted beyond
their current ledger status.

One reproducible **numerical-evaluation pitfall** was detected in the installed
mpmath 1.3.0 route: tiny-step numerical differentiation of polylogarithm order
at a positive integer, with a negative argument outside the unit disk, did not
retain the requested precision in the recorded example. The package provides
`code/differentiation_pitfall.py` and `data/differentiation_pitfall.json`.
At 50 working digits the observed discrepancy was about 2.05e-9. The reference
was replaced by the differentiated defining Fermi integral, independently
matched to complex-ray Borel quadrature. This is an observation about that
route/version, not a diagnosis of the library's internals or a claim that all
numerical differentiation is defective.

## Safeguards for this contribution's integration

**Terminated does not mean exact.** At integer m, the algebraic expansion is a
polynomial, but the exact function also contains `-(-1)^m T_m`. Its perturbative
Stokes jump vanishes while its physical exponential tail need not vanish.

**Differentiate before discarding a resonant zero.** A coefficient that is zero
at integer order can have a nonzero, factorially growing order derivative.
The exact Gamma detuning identity and the Bell formula specify these jets.

**Fix the side of the contour, not only the sign symbol.** Here an upper Borel
path gives argument `-pi` to `1-(xi+i0)/n` past its branch point. The upper-minus-
lower jump of the first-jet Borel integral is `-2*pi*i*(-1)^m T_m`.

**Keep the zero Fourier coefficient.** Periodic residues need not have zero
mean. The finite digamma resolvent is subtracted before summation and its
cyclotomic tail includes p=0. The period-three example makes this explicit.

**A sufficient disk is not an exact radius.** The generic Rouché certificate
only proves convergence on its certified disk. The exact dilogarithm radius
additionally uses positive coefficient iteration, a genuine fold, exclusion
of every other singularity on the circle, and local complex continuation.

**Arithmetic averaging is not nonlinear-compatible summation.** The repository's
Stokes-transport source already discusses the averaging defect. Proposition
10.1 repeats the elementary local obstruction as a safeguard, not as a new
discovery and not as a refutation of Écalle median summation.

**Respect proof scopes.** The sharp physical convergence theorem applies to
`y > pi^2/6` in the stated quadratic-core coordinate, with convergence exactly
for `y >= pi^2/4`. It does not deny existence of the inverse below that value.
The general feedback theorem covers interior folds only. Research Question 1
contains a proposed boundary coefficient law, explicitly not proved here.

## Evidence hierarchy

The article gives conventional all-order proofs. The exact Python/SymPy checks
are finite regression tests. High-precision quadrature and root comparisons are
floating-point diagnostics, not interval certificates. Larger-sector tests use
binary64. Printed zero errors indicate agreement at the working precision.
No Lean formalization, interval enclosure, external referee approval, exhaustive
repository audit, or worldwide novelty certification is claimed.
