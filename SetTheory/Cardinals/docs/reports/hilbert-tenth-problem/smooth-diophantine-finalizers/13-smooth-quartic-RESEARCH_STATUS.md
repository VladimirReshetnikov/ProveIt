# Research and verification status

## Proved in the article

1. Exact-degree-four finalization of an arbitrary quadratic integer system,
   adding five variables, with a natural-zero bijection and a two-copy signed
   integer-zero bijection. Heights and bounded-box counts transfer exactly.
2. An explicit integral Bezout identity for the equation and its derivatives,
   with coefficient degree at most four and product degree at most seven.
   This proves relative smoothness over Z and over arbitrary coefficient bases.
3. Geometric integrality of every fibre. The characteristic-two fibre is affine
   space of dimension n+4.
4. Constructible nonnegative dyadic points of controlled rational height;
   integral points at every prime; solutions modulo every positive integer.
5. Rational points dense in the real locus and Zariski dense in the variety;
   exactly two real path components.
6. A total-weight classification for universally smooth weighted-guard
   finalizers when the first guard weight is one: the only totals are 4 and 16.
7. A dyadic obstruction for weights (1,3), proving that three guards (five
   auxiliary variables total) are necessary in the positive weight-four family
   if both universal smoothness and universal dyadic solubility are demanded.
8. A complete quadratic frontend for externally bounded deterministic counter
   runs, with unique natural witnesses and explicit size formulas.
9. Computably enumerable completeness of integer/natural solvability on the
   compiled class, conditional only on the established MRDP background theorem.
10. A higher-degree power-of-two homogeneous extension, proved but not implemented.

## Recorded implementation checks

`python code/verify.py` completed successfully with 21,128 assertions under
Python 3.13.5 and SymPy 1.14.0. These include actual expanded symbolic identities,
finite exhaustive comparisons, exact rational substitutions, local congruence
checks, independent sparse evaluation, and malformed-input rejection checks.
The exact ranges and full assertion counts are supplied in the article and JSON.

The counter example has 24 source variables, 28 residuals, and a 29-variable
quartic with 97 monomials. The horizon is 3. Only the constant five-variable
finalizer is independent of the source or horizon.

## Known background, not claimed as new

MRDP; smooth-variety undecidability (in particular Poonen's construction);
arithmetic-circuit lifting; the classical four-square theorem; the hypersurface
Jacobian criterion; rational parametrization of a quadric with a rational point;
and elementary counter-machine simulation methods are established background.

The five-variable formula, combined guarantees, explicit identities, and
restricted guard obstruction were developed here. Their exact publication
priority is not established. The targeted source search was not exhaustive.

## Not established

- No general single-fold or finite-fold MRDP theorem.
- No fixed-arity unique encoding obtained from the bounded counter frontend.
- No algorithm deciding arbitrary integer, rational, or dyadic equations.
- No smooth proper model over Z, and no claim that the naive projective closure
  is smooth.
- No universal density theorem for dyadic points.
- No global lower bound of five auxiliaries outside the stated weight-four family.
- No total-degree-four master polynomial with all input fibres relatively smooth;
  the direct parameter-as-coefficient presentation is quartic in witnesses and
  at most degree six jointly with a linearly loaded input.
- No Lean/Coq verification, repository-wide build, or new axiom audit.
- No improvement to the repository's universal arithmetic-operation records.
- No publication, peer review, or exhaustive novelty certification.

## Development note

An intermediate four-identical-guard construction used six additional variables.
The delivered paper and software use the smaller weighting (1,1,2), with five
additional variables. The equal-guard variant is discussed only to explain the
weight classification and the compression; it is not the delivered compiler.
