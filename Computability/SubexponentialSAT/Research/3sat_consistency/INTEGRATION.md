# Suggested integration

This is a research packet, not a change to the trusted Lean development.

A suitable repository location is
`Computability/SubexponentialSAT/Research/sat_support_consistency/`.
Keep the report, source, data, checkers, results, and provenance together.
Preserve the original external source manuscripts and their stated proof
status. This archive does not supply Lean proof terms for its new inequalities.

Suggested index description:

> Degree-aware schedules and support-consistency certificates. A strict
> 10→13→7 schedule gives eventual normalized time/space coefficients
> 13.690/12.798 for degree at most s^0.51, compatible with the already known
> square-root-degree 3-SAT regrouping. The time gain is a composition of
> existing primitives; under that same schedule the earlier pair certificate
> gives the same time coefficient. New zero-sum support potentials additionally
> improve the generic degree-s^0.9 cached coefficients to
> 29.7460571/28.3295782 and certify the tighter simultaneous storage bound.
> Includes exact witnesses, independent reconstruction, full recursion,
> narrowly stated representation barriers, and a finite contraction prototype.
> Uses subexponential space; no smaller unrestricted SAT exponent order and no
> new Lean formalization are claimed.

The integration should preserve two distinct comparison tables: one for the
generic degree-s^0.9 interface, and one for degree promises actually supplied
by the 3-SAT reductions. The earlier polynomial-space branches and the
stronger s^(1/12) branches remain separate resource/regime options.

Before accepting a future implementation, maintain the paid singleton-entry
term in the recursion, select one plan for both time and space, use exact
integer plan comparisons, retain creation-precision semantics, and recheck
the stage-specific degree gates. The packaged finite prototype is not a
substitute for implementing the inherited deformation or fast matrix backend.
