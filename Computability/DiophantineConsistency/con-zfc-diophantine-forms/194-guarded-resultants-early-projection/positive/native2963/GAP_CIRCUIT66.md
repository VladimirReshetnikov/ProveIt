# Checked literal H2082 circuit counts

`GapCircuit66` supplies the literal binary arithmetic DAGs from the coherent
compact54-sharp H2082 candidate. Lean checks every backward reference, every
node's path to the output, all nine input leaves and all eleven fixed leaves.

| Circuit | Nodes | Add | Subtract | Multiply | Live binary operations |
|---|---:|---:|---:|---:|---:|
|Positive coordinates|477|158|22|263|443|
|Natural coordinates|484|166|21|263|450|

Both lists also have14 integer-literal leaves. Fixed leaves are independent
parameters in this module, so counting does not assume a coefficient
calibration or a higher-level scalar recipe identity. `eval_positivePolynomial`
and `eval_naturalPolynomial` connect the actual DAGs to their actual
`MvPolynomial` data for every supplied eleven-integer tuple. The scalar
ring-homomorphism identities hold over every commutative ring.

`tools/generate_gap_circuit66.py` reads only inert JSON with these exact pins:

| Input | SHA256 |
|---|---|
|gap2082_positive.json|`7a34fddb23453755a26c9185f3540d99bc7697848e037fecbaa20fc2df7631a9`|
|gap2082_natural.json|`be7d9e1285a1cf674978058c3b1be2f27a17af9c0d0bdc6e4f8310481a40d001`|

The generator independently checks topology, all-node liveness, input and
fixed-name coverage, the source/layout bindings and all operation counts.
It reuses only the generic Lean output template from the frozen earlier
circuit generator, without modifying that generator or its data. `--check`
reproduces `GapCircuit66.lean` without writing. Finite Lean certificates use
`decide +kernel`; all16 dedicated theorem audits contain only standard axioms.

This module proves exact literal counts and polynomial evaluator semantics.
The subsequent [coherent four-port binding and counted-DAG identification](GAP_CIRCUIT_RECIPE66.md)
with `GapNinePolynomial66` now pass Lean, as does the
[cancellation-aware degree upper bound](GAP_DEGREE66.md). Native
ZFC-refutation calibration and the internal ZFC biconditional remain separate
obligations.
