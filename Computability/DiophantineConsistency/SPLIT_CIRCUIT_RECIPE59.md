# Counted split116 circuits identified with the scalar equation

`SplitCircuitRecipe59.naturalValue_eq_recipe` proves that the literal
480-operation natural parent circuit evaluates to
`SplitNinePolynomial59.value`. This is an identity over every commutative ring.
`jointNaturalValue_eq_recipe` identifies the independently checked
463-operation circuit with that same scalar expression.

The stronger endpoints `naturalPolynomial_eq_recipe` and
`jointNaturalPolynomial_eq_recipe` identify the actual `MvPolynomial` data.
They hold for every integer four-port tuple and every natural height exponent
`a`, with height `2^a` and threshold scale `2^(8*a+85)`. Consequently the
operation counts apply to the polynomial already connected to the literal
old-z source equations by `SplitNinePolynomial59`; agreement on sample inputs
is not a premise.

The twelve fixed leaves are bound together by
`SplitCircuitRegisters59.fixedLeaves`. In order they are

```
2*K, -2*beta, -2*K, -2-2*K, 2*beta+2*beta*K, -4*beta,
2*beta-2*MC-2*MF, -beta, -2*beta^2,
2*beta^2-2*beta*MF, 4096*height, thresholdScale.
```

Here the four ports are ordered `beta,K,MC,MF`. There is no independent choice
of one fixed coefficient or one port from another tuple.

The proof follows the actual node list locally. `SplitCircuitSteps59` derives
515 register equations from the evaluator's node-equation theorem and proves
107 pure-source-base power identities. `SplitCircuitRegisters59` checks the
three Horner kernels against all 7, 39 and 43 coefficient records, then checks
the base, masks, source words, source rank, threshold and margin scale.
`SplitCircuitRecipe59` joins 24 further named tail registers to the scalar
recipe. Its small ring identities account for the alternative formulas for
`Q`, `E`, the third Pell norm, the first finalizer radicand and the final norm.
The proof keeps earlier named values opaque; it does not expand the full
high-degree polynomial.

The inert natural parent JSON is pinned to SHA256
`cb0caa3a14370e9a5d43be9cabbfef86f92481301b09f4fd7bc7c19f550804db`.
The three generators `generate_split_recipe_steps59.py`,
`generate_split_circuit_registers59.py` and
`generate_split_circuit_recipe59.py` reproduce their respective Lean files;
`--check` compares without writing. Their finite inputs ultimately use the
same SHA-pinned parent reader as `generate_split_circuit59.py`.

Dedicated checks compile every stage and audit the public source-register
and polynomial identities. Only `propext`, `Classical.choice` and `Quot.sound`
occur. The source data and all arithmetic identities are supplied explicitly;
there are no new axioms or native-evaluation proof shortcuts.

This identification discharges the counted natural DAG-to-scalar-recipe
obligation. It does not calibrate a native compiler tuple to a ZFC refutation
predicate or prove the object-language ZFC biconditional. The positive-input
translation and both 473/456-operation positive recipe identities are checked
in the subsequent [positive stage](SPLIT_POSITIVE_RECIPE59.md).
