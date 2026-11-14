# PA194 parameterized function-child history

`PA194TermHistory.lean` defines explicit PR decoders for the argument vector
and its first two entries in the numerical function-term constructor
`pair 2 (pair arity (pair symbol vector)) + 1`. Certified pairing projections
are required; their existential availability is established in
`PA194StackCode`. It proves exact decoding equations in every candidate-PRA
model for a present first or second argument. The arity, symbol, argument
codes, and remaining vector fields may all be nonstandard model elements.

`first_lt_function` and `second_lt_function` show each such child is strictly
smaller than its enclosing function code without requiring standardness or
well-formedness of those fields. `modelFirstLookup` and `modelSecondLookup`
combine the decoders and bounds with the parameter-preserving course-of-values
history to retrieve each previously computed child while preserving arbitrary
closing-label and binder-depth parameters. The numeric equations require no
IΣ₁ assumption.

The history update code is still a parameter. These results do not construct
the full recursive syntax traversal or show that arbitrary encoded values are
well-formed terms. They do not identify Foundation typed syntax in candidate
PRA or prove a consistency implication. The underlying history is described
in [PARAM-HISTORY.md](PARAM-HISTORY.md).

Run from the repository root with the audited overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-term-history.sh
```
