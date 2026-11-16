# Lean formalization outline

`FiniteCore.lean` contains the exact natural-number recursors and elementary
induction targets.  `AnalyticContracts.lean` exposes every analytic side
condition as finite data rather than hiding it behind classical real analysis.
`ObjectLanguageTargets.lean` gives the concrete endpoint in ProveIt's
`Prf PRAAx` and a module dependency order.

The intended implementation order is:

1. Port `fac`, `gPos`, finite products, hyperfactorials and the `c_k`
   coefficients to `PR` symbols and prove their equations with `PRA.qfInd`.
2. Reuse the rational, bounded-sum, pairing and simultaneous-recursion modules
   in `IPRADerivations`.
3. Import the product, exponential, logarithm, Gamma, Euler-constant and
   Stirling contracts from the existing `gamma_ipra` packet, replacing every
   host-level contract by an object-language checker theorem.
4. Implement the single canonical-factor estimate and its derivative variants.
5. Build the product evaluator and prove normalization, zeros and the functional
   equation.
6. Compile the Taylor, integral, reflection and multiplication identities by
   finite telescopes and branch/separation certificates.
7. Implement Euler--Maclaurin with a fixed truncation order and Nemes' explicit
   remainder bound for the asymptotic module.
8. Add `#print axioms`/repository checks only after the theorems have type
   `[] ⊢[PRAAx] phi`; host-level kernel checks alone are not the goal.

The files in this archive were not compiled because the build environment did
not provide Lean.  They are therefore a detailed scaffold, not compilation
evidence.
