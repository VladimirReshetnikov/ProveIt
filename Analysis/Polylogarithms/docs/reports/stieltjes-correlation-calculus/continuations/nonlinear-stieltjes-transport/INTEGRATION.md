# Proposed ProveIt integration

## Destination and dependency order

Suggested standalone report destination:

`Analysis/Polylogarithms/docs/reports/nonlinear-stieltjes-transport/`

This is a proposal, not an assertion that the directory already exists. Preserve the entire package there, or use the repository's current intake convention. Add its source and evidence entries to the source inventory and editorial ledger only after the normal mathematical review.

For the canonical manuscript, place a nonlinear-coordinate section on the Hurwitz/Stieltjes/Gamma spine **after** the fixed-coordinate periodic Stieltjes extension and derivative-anomaly results. The source organization is changing into four volumes; consult the current driver rather than duplicating a chapter. `integration/manuscript_insert.tex` is a self-contained starting point. All labels and local helper macros are prefixed `nonlinear:` or `NL`; the environment is `nonlinearthm`. Adapt its counters to the manuscript's conventions during integration.

Dependency sequence:

1. Unit-coordinate Hadamard definition and density pullback.
2. Universal logarithmic transport and cocycle.
3. Lagrange transport of existing delta derivatives; two-endpoint reflection signs.
4. Stieltjes singular expansion, harmonic transport, tangent-coordinate vanishing.
5. Previously established periodic Fourier generator with **full** `P_p(u)` subtraction.
6. Nonlinear circle map, Poisson average, scalar coordinate correction.
7. Ordinary subtracted identities and mean-zero primitive hierarchy.

## Proposed ledger entries

- **Proved, ordinary analysis:** finite-jet formula for `x^-k log^n x`, for all finite integer pole/log orders and positive-slope smooth coordinates.
- **Proved, ordinary analysis/algebra:** explicit lower contact derivatives and exact transport of an already proved contact comparison. This transports the correlation distribution; it does not identify nonlinear pullback with convolution of pulled-back factors.
- **Proved:** all-index Stieltjes harmonic transport and sharp universal cutoff `m >= 2p` for tangent coordinates.
- **Proved:** local closure of finite Stieltjes products. This is not a global reduction of product integrals.
- **Proved:** all nonlinear circle averages in the named finite-part convention, their odd-order rational polygamma subfamily, and ordinary convergent examples.
- **Proved:** unique mean-zero periodic primitive hierarchy and its ordinary nonlinear averages.
- **Replayed finite evidence:** 504 exact assertions and 47 high-precision diagnostics; not proof-assistant verification or certified transcendental residual enclosures.
- **Still open:** general simultaneous collision-diagonal restrictions, arithmetic independence, general unequal-map correlations, and the restricted Gaussian S6 reduction.

## Normalization checklist

Keep `gamma_0 = -psi`, spectral derivative signs, unit logarithmic scale, and the density Jacobian. For a right endpoint use `phi_-(t)=1-phi(1-t)` and reflect delta derivatives with sign `(-1)^j`. The circle map requires the continuous arctangent branch on both halves of the interval. Mean-zero periodic primitives are not interchangeable with the zero-based negative-polygamma convention without a change-of-normalization polynomial.

No live GitHub write was performed. The package contains no automatic upload or repository mutation script.
