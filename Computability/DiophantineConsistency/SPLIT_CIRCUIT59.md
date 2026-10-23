# Checked literal parent circuit for the split116 source

`Lean/DiophantineConsistency/SplitCircuit59.lean` transcribes the two inert
compact54-sharp circuit JSON files. Its generator pins the positive SHA256
`c3d16f56ca868cf1a0773889ed06e89a865ea41057497467325ef2c09e7de96f`
and natural SHA256
`cb0caa3a14370e9a5d43be9cabbfef86f92481301b09f4fd7bc7c19f550804db`.
The original files are in
`candidates/split116-compact/compact54-sharp/generated/`.

| Circuit | Nodes | Add | Subtract | Multiply | Live binary operations |
|---|---:|---:|---:|---:|---:|
|Positive|508|162|22|289|473|
|Natural|515|170|21|289|480|

Lean checks every table entry's reference bounds and strict topological order.
Every non-output node has a literal later-consumer witness; the generic
`reaches_of_laterConsumer` theorem proves that each node has a directed path to
the output. Thus the operation counts include exactly live binary nodes. Each
circuit has nine distinct input leaves, twelve distinct fixed leaves and
fourteen integer literal leaves. No multiplication by a literal is free.

The input order is `b,g,h,s,w,C,i,j,n`. Fixed leaves are parameters in this order:

```
c001 c004 c005 c006 c007 c008 c010 c011 c015 c016 base_scale threshold_scale
```

The module retains all named-node indices for subsequent semantic certificates.
`positiveValue` and `naturalValue` evaluate the actual lists of nodes, with
shared earlier values. `positivePolynomial` and `naturalPolynomial` construct
multivariate integer polynomials from the same lists. The two `eval_*Polynomial`
theorems prove that polynomial evaluation equals the scalar circuit evaluator.
These results hold for every supplied twelve-integer tuple.

`ArithmeticDAG.lean` supplies the generic evaluator, ring-homomorphism theorem,
liveness proof and polynomial interpretation. `ArithmeticDAGSemantics.lean`
proves that actual evaluator values satisfy every local node equation and that
a proposed node-value table satisfying those equations determines evaluation
uniquely, under topology. This supports local transformation certificates
without expanding the full multivariate polynomial.

The generator uses only inert JSON and the Python standard library:

```
python3 tools/generate_split_circuit59.py --check
```

The finite Lean checks use `decide +kernel`, with no `native_decide` axiom.
Dedicated checks for all three modules pass; their axiom audits contain only
Lean's standard `propext`, `Classical.choice` and `Quot.sound` (some results
require fewer).

These counts belong to the literal parent DAG.
[SplitCircuitRecipe59](SPLIT_CIRCUIT_RECIPE59.md) now proves the natural
parent's equality with the higher-level `SplitNinePolynomial59` recipe,
including all twelve fixed-leaf expressions in the four source ports and
height/threshold scales. The positive-input translation, native calibration
to refutation, internal ZFC provability and global simplicity optimality
remain separate obligations. Newer local candidate DAGs need their own data
and transformation certificates.
