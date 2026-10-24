# The counted H2082 circuits implement the checked equation

`GapCircuitRecipe66.naturalValue_eq_recipe` proves that the actual
450-operation natural circuit evaluates to `GapNinePolynomial66.value` over
every commutative ring. `naturalPolynomial_eq_recipe` proves equality of the
actual `MvPolynomial` data for every supplied four-port tuple and half-height
parameter. Thus the checked operation count belongs to the polynomial already
proved source-equivalent by `GapNinePolynomial66`.

`GapCircuitRegisters66.fixedLeaves` binds all eleven fixed leaves together.
In their actual DAG order they are

```
4096*height, 2*K, -2*K, -2-2*K, 2*beta+2*beta*K,
-2*MC-2*MF, -4*beta, -beta, -2*beta*MF, -2*beta^2, scale.
```

The height is `2^(2*a)` and the threshold scale is `2^(15*a+79)` in the
polynomial theorem. These are ordinary integer constants after `ports,a` are
supplied. The base and threshold recipes therefore match the coherent H2082
candidate, including the absence of an extra `b` factor in the threshold.

The proof follows the literal node lists. `GapCircuitSteps66` supplies484
local gate equations and86 pure-base power identities. The thirteen source
register identities check all6/36/43 kernel records, the masks, source words,
rank, base, threshold and margin scale. The scalar recipe proof joins24
further tail registers, keeping previously named expressions opaque. Small
ring identities handle the alternate formulas for `Q,E,I,a0` and the final
norm. No full output-polynomial normalization is used.

`GapCircuitTranslation66.positiveValue_eq_naturalValue` proves the exact
443-operation positive circuit equals the 450-operation circuit with all nine
inputs decreased by one. A finite reference certificate checks every retained
node; the input/translation prefix is checked directly and one multiplication
uses commutativity to reverse operand order. `GapPositiveRecipe66` then gives
the actual positive scalar and polynomial identities, with internal
`j=positiveInput7-1`. Its root-equivalence theorem supplies both directions of
the positive-natural versus unrestricted-natural coordinate translation.

`GapCircuitTail66` exports six short identities for the actual evaluator's
`D,E,F,I` registers, their Pell product and the final norm output. These facts
hold for every eleven-leaf tuple and support degree reasoning without
unrolling the circuit or duplicating the scalar source recipe.

The four new generators `generate_gap_circuit66.py`,
`generate_gap_recipe_steps66.py`, `generate_gap_circuit_registers66.py` and
`generate_gap_circuit_recipe66.py` reproduce their respective Lean files with
`--check`. Their inert DAG pins and exact443/450 live-operation counts are
recorded in `GAP_CIRCUIT66.md`. Dedicated checks audit the source, tail,
polynomial, input-translation and root-correspondence theorems; only standard
Lean axioms occur.

This closes the counted-DAG-to-source-equivalent-polynomial bridge for the
443/450 family. The cancellation-aware Lean degree upper bound is recorded
in [GAP_DEGREE66.md](GAP_DEGREE66.md). Exact degree, whole-tuple native
calibration to ZFC refutation and the object-language ZFC biconditional
remain separate stages.
