# Verification boundary

## Mathematical result

The report gives a human proof of a conditional iPRA theorem schema for
fixed primitive recursive presentations. Its assumptions are local numerical
regularity, derivative, positivity, chart, incidence, and fan-order
contracts. Green's identity, triangle turning, and the global angle sum
are proved from those contracts rather than being assumed.

The output is a primitive recursive family of rational inequalities with an
explicit error budget. Interpreting its regular names gives the smooth
Gauss–Bonnet formula. The general piecewise formula and the finite residual
assembly theorem are also proved.

## What was executed

1. `tools/finite_certificate.py`: exact `Fraction` checks of finite surface
   incidence, valid and invalid links, arbitrary rational residual assembly,
   and cone-metric examples, including a nonorientable projective plane.
2. `tools/discrete_green.py`: exact rational checks of FTC and discrete
   Green, their error bounds and rounding constants, high-precision shared
   node evaluation, wrong-sign rejection, and polynomial triangle pullbacks.
3. `tools/smooth_examples.py`: exact rational conformal integrals and 34
   symbolic spherical identities. Independent 1D and 2D quadratures use
   50-digit working precision; they are diagnostics, not interval proofs.

The JSON files record these actual executions. They do not certify arbitrary
input metrics, prove the whole mathematical argument, or establish the
soundness of an iPRA proof checker.

## Lean status

No Lean/Lake/Elan executable was available. Both `.lean` files are uncompiled
candidates. They contain no admitted proof declarations or new axioms, but
have no successful compilation receipt. The candidate deep bridge covers
only small finite polynomial/error-combination steps. Variable-length mesh
counting, the analytic finite lemmas, gluing and semantic adequacy still need
Lean implementation as described in the report and blueprint.

The repository's existing source and documented verification boundaries
were inspected at commit `d36b35eed5bd01af4ade66bf539622495813ccc8`; the
repository was not independently rebuilt here.

## Review

Independent mathematical review checked the curvature signs, explicit angle
branches, nonorientable seam cancellation, finite fan ordering, local-to-global
residual identity, and precision accounting. Corrections incorporated into
the report include distinguishing speed from arclength, reserving auxiliary
FTC evaluation slack, explicitly coding the edge opposite-side condition,
and allocating a local proof precision from the global precision schedule.

The final PDF was compiled from the included source and rendered for visual
inspection. A machine-readable final build/inspection record accompanies
the report in `validation/build_record.json`.
