# Common arithmetic substitution witness ceiling

`uniform_substs_witness_bound` specializes the existing unconditional
`PA196PASubstitutionWitnessComplete.wb_substsGraph` theorem. In every
candidate-PRA model with IΣ₁ arithmetic reduct, for each model element
`ceiling` there is one model element `bound` that bounds the existential
witnesses in the arithmetic-language `substsGraph ℒₒᵣ` for every graph input
whose three components are at most `ceiling`. Here “bounds” is the exact
`StrictSigmaOneInduction.bnd` formula used by the existing witness-bound
calculus. Monotonicity supplies a shared bound for all those input tuples.

`qVec_trace_and_substs_ceiling` combines that result with the fixed-ceiling
arithmetic qVec trace: for any seed and model-internal length, the trace has
one majorant for all its entries and there is one substitution-graph witness
bound for every graph argument tuple beneath that majorant. Both statements
include nonstandard model elements.

The exact bounded arithmetic substitution graph is proved Σ₀ by
`arithmetic_substs_bounded_is_sigma0`. More generally,
`bounded_graph_pair_is_sigma0` shows that two arbitrary Σ₁ graphs with the
same input arity, bounded by the same last parameter, have a Σ₀ conjunction.
A model-supplied bound can therefore occur as a fixed parameter in this
bounded graph matrix; this does not yet prove the complexity or correctness
of the complete substitution-agreement invariant.

The underlying `WB` statement existentially supplies an arbitrary
model-level monotone bounding function. This package does **not** construct a
fixed finite PRA code or definable selection for that function, and does not
establish that a desired whole invariant is Σ₁. It also does not bound the
unported PAeq substitution graph or formula-translation graph, or prove
substitution agreement or PA194 machine calibration.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-substs-ceiling/check.sh
```

The final module passed a fresh suffix check using the qVec result, retained
PA196 witness-bound prerequisites, and audited project and Foundation
objects. Its printed axioms contain no `sorryAx`. The full prerequisite-prefix
replay remains pending.

An independent suffix replay rebuilt the bounded-graph module against the
separately checked qVec ceiling and retained PA196 prerequisites. It passed
without `sorryAx`; this was not a full prerequisite replay.
