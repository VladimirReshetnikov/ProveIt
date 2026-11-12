# Proposed small literal cut for the 74 first factor

This source-only alternative makes the literal first-factor syntax explicit
before evaluating it. The cut contains only the required beta, J/w/s/r/eta/
zeta slots and arithmetic; it omits the rank, main, auxiliary and guard
branches. Its proposed `first_shape` is a literal definitional equality and
`first_eval_small` has the same statement and beta-cast premise as the reviewed
`FirstFactor74Draft.first_eval`.

This is a preventive source restructuring for a possible elaboration or
resource hazard in unfolding the whole graph. No failure has been observed and
no Lean run has established that either proof elaborates, that the cut is
faster, or that it reduces memory. The existing reviewed client and root74
chain are untouched. Applying this alternative would require a separate source
refactor, dependency review and guarded build. Provider compatibility, iPRA,
physical byte and PDF binding remain open.

Independent source review: [74 first-factor small cut](../../reviews/ordinary14-74-first-factor-small-cut-independent/README.md).
