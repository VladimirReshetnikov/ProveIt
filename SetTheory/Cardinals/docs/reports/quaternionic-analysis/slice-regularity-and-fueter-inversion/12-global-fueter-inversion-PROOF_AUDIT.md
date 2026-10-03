# Internal proof audit

This is an internal mathematical audit, not a referee report or a proof-assistant
certificate. The article contains the proofs; this file highlights dependencies
and the points at which an overbroad reading would become false.

## Dependencies

1. **Radial forward map and calibrations.** Proved using radial commutators,
   planar harmonicity, and Cauchy–Riemann equations. These are classical results.
2. **Polynomial current and Hermite identity.** Inherited from ProveIt's source
   11 and rederived here. The all-h proof reduces an arbitrary h-jet to real
   polynomials of degree at most 2h+1 by two-node interpolation. Its finite
   dimension reduction is a proof for each arbitrary h, not empirical testing.
3. **Real-axis confluence.** The contour remainder formula is polynomial in the
   formal variable. Its coefficients are real analytic at coalescing nodes;
   the confluent value is a Taylor polynomial of order 2h-1. Intrinsicness is
   essential to matching the conjugate-node data.
4. **Global inverse criterion.** Zero periods imply coefficientwise path
   independence. Evaluation of the primitive at t=z is holomorphic by the
   (t-z)^h factor in its anti-holomorphic derivative. Hermite uniqueness and
   injectivity of the current then identify the forward image.
5. **Arbitrary period realization.** Imports ordinary degree-one de Rham theory
   and global smooth additive Cousin/bar-partial solvability on planar domains.
   The proof constructs real-polynomial transition cocycles, solves them
   holomorphically, and applies the forward map. The difference between the
   target current and the prescribed closed form is explicitly exact.
6. **Reflection compatibility.** Averaging preserves an invariant homology
   character. Local primitives and Cousin solutions are chosen equivariantly.
   On fixed disks the holomorphic stems are intrinsic before applying the
   Fueter operator.
7. **Topological quotient.** The target equations define a closed Fréchet
   subspace. Each period is continuous. Surjectivity and the open mapping
   theorem identify the actual quotient topology with the countable product.
8. **Continuous norm and nonsplitting.** Local inverse formulas imply analytic
   target coefficients, so vanishing on one disk implies vanishing everywhere
   on the connected domain. This turns a compact supremum seminorm into a
   continuous norm. The classical product-neighborhood argument excludes a
   continuous homogeneous section at infinite admissible period rank.
9. **Positive sections.** Openness yields arbitrarily small exact lifts of
   sufficiently late coordinates in any one fixed seminorm. Amplitude-dependent
   interpolation gives a continuous nonlinear series. Fixed-envelope lifts
   instead give a continuous linear series with geometric seminorm tails.

## Specific error traps checked

- The coefficient module is nonzero, finite dimensional, real, and orthogonal.
- Central i is distinct from a Clifford imaginary unit.
- Kernel coefficients are real, not arbitrary complex coefficients.
- The symmetric target is smooth through the axis and has even/odd parity.
- Reflection preserves the period character on homology but reverses the
  orientation of a counterclockwise generator.
- For a conjugate pair, the invariant basis vector divided by two has the same
  character value as the upper counterclockwise generator.
- A real annulus and C minus the integers have no admissible period obstruction,
  despite having nonzero or infinite ordinary first homology.
- Infinite period data form a product, not a direct sum.
- The normalized compatible inverse and a section of the period map are
  different operators. Only the latter fails to split linearly at infinite rank.
- The no-derivative conclusion assumes the directional derivative is a continuous
  linear operator on the full product space; it does not prohibit all weaker
  notions of regularity on restricted input classes.
- The nonlinear series uses amplitude-dependent lifts. A single fixed lift per
  coordinate cannot give a continuous linear section on the entire product.
- Weighted sections depend on the chosen envelope. No interchange of the
  quantifiers 'for every envelope' and 'there exists a section' is asserted.
- Compact-seminorm control is not a boundary-norm or physical-energy estimate.

## Verification limits

The code checks polynomial identities in finite ranges and numerical contour
integrals. It does not check Cousin solvability, arbitrary homology characters,
infinite sums, or uniqueness in a proof assistant. Those assertions are
supported by the written proofs and the stated classical inputs.

No independent review, formal verification, or historical priority claim is
implied by this audit.
