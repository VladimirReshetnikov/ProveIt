# Integration notes

This is a new research package for review and incorporation into ProveIt.
The delivery does not modify any remote branch, issue, or pull request.

Suggested package name: trace-linear-radical-projections.

## Authoritative equations

- Compact principal: compact/equations/trace87_degree232.json,
  with the whole compact/coefficients tuple and its reconstruction.
- Sparse integer principal: direct/equations/self_power236/equation.json.
- Integer dimension companion: direct/equations/shared_error234/equation.json.
- Intermediate tradeoff: direct/equations/self_power235/equation.json.
- Other compact tradeoffs are listed in compact/RESULTS.json.

Preserve each domain. Ten positive integers are not ten unrestricted
integers. Do not bind individual native ports from different tuples together.

## New reusable mathematical statements

1. trace_linear_auxiliary_congruences: if f=1+c*d, the expression
   f*(c*T-R)-c has residues -c modulo f and -R modulo c.
2. trace_linear_parent_map: the polynomial d=(f-1)/c,
   Tnew=f*Told-d*R, and the stated transport adjustment preserve the
   entire polynomial. Positivity is proved on parent positive zeros.
3. label_balance_self_power: at F=t^t, evaluated label-product
   equality recovers exact positive-label multiplicities.
4. common_radical_monic_projection: a unit coordinate in the common
   residual Hessian kernel and a unit row slope give an integral
   polynomial zero-set bijection, preserving degree at most two.
5. Concrete terminal Hessian certificates: the three final stacked
   Hessians have full column rank modulo 101.

## Review boundary

All new finite transformations and coefficients have exact executable
checks. The ordinary unbounded arithmetic proofs are in the paper and
component PROOF.md files. Their consistency conclusions compose the
named inherited calibration; no new complete formal-assistant proof is
asserted.

The modular rank result blocks only additional projections through the
same common-quadratic-radical mechanism in the final chart. It is not a
minimality theorem for arbitrary equations or nonlinear transformations.

Retain predecessor packages and their provenance and distinct
support/height/domain tradeoffs.
