# Proof and verification status

## Written results

- The all-order density theorem is proved for any locally finite ordinate
  multiset satisfying the stated two-term counting law with logarithmic
  remainder. It includes every fixed spatial derivative and a full-line
  uniform error.
- The Dirichlet specialization uses the established zero-counting theorem.
  RH/Dirichlet GRH identifies its integer exponents with the real parts of
  Li coefficients. The ordinate-defined process theorem needs no RH premise.
- The sampling example is unconditional. Its coefficients are positive real
  numbers at integer indices, not integer-valued coefficients.
- Its Mellin continuation is proved on `Re(s) > -1`. It is not asserted to
  satisfy the repository's stronger whole-plane `IsPolar` definition.

## Review completed

Separate mathematical derivations checked the symbol normalization,
Lambert scale, all-order Fourier error, first three profiles, circle trace,
moment transition, positive coefficient bounds, interpolation error, and
Mellin pole. This is internal review within the present analysis, not
external peer review. The detailed review is in the source-audit directory.

The executable checks verified:

- an exact symbolic second-derivative identity;
- 15 Gamma-derivative profile identities against numerical quadrature;
- 9 exact-scale identities at high precision;
- 30,000 bounded-weight samples in the main program;
- independently, 3,000 coefficients and sample/interpolation identities at
  80 decimal digits in the sampling program.

## Formal verification

The new results have not been compiled in Lean, Rocq, or another proof
assistant. No `sorry`-based outline is represented as a formal proof.
The upstream Lean files are preserved as source snapshots. We inspected
their statements and key interfaces; we did not independently rebuild the
entire GRH development. Its formal verification is supported by the primary
external verification reports cited in the PDF.

## Quantifiers and limitations

- Multiplicities and central zeros are allowed.
- Complex Dirichlet characters require `Re(lambda_chi(n))`.
- The asymptotic constants depend on the fixed character/counting data;
  they are not claimed uniform as conductor tends to infinity.
- The real-line density expansion is uniform for all real x. The circle
  version is uniform only on each fixed bounded interval of rescaled x.
- The sampling example establishes a limitation for a positive-weight
  analytic class, not an impossibility theorem for the actual prime weights.
