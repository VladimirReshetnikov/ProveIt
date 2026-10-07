# Integration and audit plan

## Placement

Recommended:

`Combinatorics/Ramsey/Research/GowersSzemeredi/quadratic-barrier/`

The package may instead be incorporated as a new source of the existing
local-quantitative-refinements report. Preserve the article's theorem labels and
its precise comparison with source 20. The mathematical statements are research
proofs, not already checked Lean companions.

## Main statement identifiers

The labels below are stable LaTeX labels, independent of printed page numbers.

- `thm:prime`: prime-cyclic indicator saturation, every fixed `k >= 3`, `d >= 2`.
- `cor:barrier`: impossibility of a uniform `o(u^2)` counting error.
- `thm:field`: indicator saturation on powers of a fixed prime field.
- `thm:partition`: the first-dependent-subset partition expansion.
- `lem:transfer`: exact signed-radix transfer of bounded Fourier moments.
- `lem:rounding`: simultaneous finite-probability rounding and exact cardinality.
- `thm:universal`: one sequence for all fixed lengths and orders.
- `prop:largerR`: improved attainable coefficient described by `K_k`.

## Suggested formal module boundaries (not implemented)

### CubeCircuitGeometry

Finite affine-rank statements for binary cube rows over odd prime fields and
characteristic zero; four-circuit classification; exact circuit count. The
partition recurrence should be separately executable.

### SpikeCircuitMoments

The exact formula

`E prod (p * 1_{L_j = 0} - 1) = sum_T (-1)^(r-|T|) p^(|T|-rank(L_T))`

and its circuit specialization. This component has no asymptotic analysis.

### TorusCircuitMoments

Haar pushforwards for full-row-rank integer linear maps and finite Fourier
orthogonality, followed by the two-frequency and flat-band local moments.

### CenteredSinePartition

Analytic logarithmic generating functions; exact one-coordinate factorization;
finite-grid centered-sine transform; support-cover cost; uniform finite-order
Taylor remainder. The needed cases are `q = 3` and `q = 4`; a first formalization
need not cover every q in the general theorem.

### SignedRadixTransfer

For positive integers C,L, set `B = 2*C*L + 1` and choose `Q > B^n`.
Prove the no-aliasing statement and use it termwise in a finite Fourier expansion.
This module can be completed independently of the analytic partition theorem.

### IndicatorRounding

Finite product Bernoulli space, cube-collision expectation bound, progression
variance bound, union bound, and an exact-cardinality adjustment. Explicitly require
admissibility for every progression length being rounded.

### QuadraticBarrier

Combine the asymptotic inputs and rounding to obtain the indicator theorem.
A theorem assuming the asymptotic inputs is conditional; its hypotheses must not
be hidden in an instance, axiom, or unproved interface.

## Audit priorities

1. Verify the exact centering cancellation before expanding: uncentered sine
   moments do not have the required all-slot support property.
2. Keep all parameters fixed in asymptotic estimates unless uniform dependence
   has separately been proved. The simultaneous theorem is a diagonal argument,
   not uniformity for lengths growing with n.
3. Keep normalized cube moments distinct from their `2^d`-th roots.
4. In cyclic transfer require integer digit bounds and `Q > B^n`; full Fourier
   coefficient vectors must not alias, not merely the one-variable frequencies.
5. Separate the random density from the final exact cardinality and recenter the
   balanced function using the actual density.
6. Report finite checks, high-precision tests, written proofs, and kernel-checked
   theorems as different verification levels.

## No repository writes performed

Neither repository was edited by preparing this package. No pull request,
commit, or library upload is part of the deliverable.
