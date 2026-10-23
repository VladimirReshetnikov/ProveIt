# Checked shared-power replacement for the split116 parent

The joint-power circuits have456 live binary operations in positive coordinates
and463 in natural coordinates. They use the same nine inputs and twelve fixed
leaves as the473/480-operation parent. Lean proves that each replacement defines
exactly the same multivariate polynomial as its parent, for every supplied
fixed-leaf tuple.

The checked endpoints are
`SplitJointPower59.positiveValue_eq_parent`, `naturalValue_eq_parent`,
`positivePolynomial_eq_parent` and `naturalPolynomial_eq_parent`. Scalar equality
holds over every commutative ring. In particular, zeros and polynomial degree
are preserved without positivity or coefficient-calibration assumptions.

| Circuit | Nodes | Add | Subtract | Multiply | Live binary operations |
|---|---:|---:|---:|---:|---:|
|Positive joint-power|491|162|22|272|456|
|Natural joint-power|498|170|21|272|463|

The improvement replaces107 multiplications computing pure powers of the source
base by90 shared multiplications. The86 required exponents include the base
itself. Five helper exponents114,256,565,1044 and1078 supply the exceptional
required exponents522,636,1201 and2279. Every remaining non-power node is
retained with an exact reference mapping.

`ArithmeticDAGPowers.lean` proves a generic certificate checker. It first
establishes the original pure-power values by induction, using topology and
`pow_add`. Each replacement node then receives either an original node value
or a certified power of the original base. A finite node-relation certificate
checks every retained literal, input, fixed leaf, operation and operand
reference. `ArithmeticDAGSemantics.value_eq_of_node_equations` turns these local
identities into equality of the actual evaluators. Instantiating this universal
ring theorem with the multivariate polynomial ring proves polynomial equality
directly; modular evaluation is not a premise.

The generator `tools/generate_split_joint59.py` pins the inert files under
`candidates/split116-joint-powers/`:

| File | SHA256 |
|---|---|
|split_116_positive.json|`83a14b00d3312f08da5ee578ab4926a2c36bff8f317145f81fd3c4b4edc60b87`|
|split_116_natural.json|`06177528b9791a93588d3843a9f894b9d8abf299c25a0faa569b3f422925562c`|
|positive_rewrite.json|`84aea2496f184c5b5640c4555a82a02fd33d3f878efbd62078891244645c8b22`|
|natural_rewrite.json|`0c2a7599e10ffbc4383903c492fc34082ceab8f24366343c87c88b41ff32f760`|

It independently derives power labels from both actual node lists and checks
all retained references before emitting `SplitJointCircuit59.lean` and
`SplitJointPower59.lean`. `--check` reproduces both files without writing them.
The finite Lean certificates use `decide +kernel`. Dedicated checks audit the
generic checker, all circuit endpoints, and all four equality theorems; only
Lean's standard axioms occur.

This is a local size reduction of the pinned parent, not a global minimum.
The natural DAG is now identified with the source/rank arithmetic recipe by
[`SplitCircuitRecipe59`](SPLIT_CIRCUIT_RECIPE59.md), including all twelve
fixed-leaf expressions. The positive-DAG shift, authentic native compiler
calibration and internal ZFC provability remain separate obligations.
