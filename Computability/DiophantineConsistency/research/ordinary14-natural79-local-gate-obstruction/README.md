# A finite obstruction to local one-gate identities

For the pinned 79-operation natural graph and the four numeric ports recorded by the external P72 coefficient files, none of the **1,084,128 candidate tuples in the specific local rewrite class below** preserves the graph's literal output as an integer polynomial. This is not a lower bound on equation size and does not rule out a different 78-operation equation with the same zeros.

A candidate is constructed as follows:

1. Select a graph node `n` with an immediate predecessor gate `c` whose only consumer node is `n`. If `n` uses `c` twice, it still counts as one consumer.
2. Delete `c` and replace `n`'s original operation by one operation `a + b`, `a - b`, or `a * b`.
3. Each new operand may be any input variable, any of the four fixed port leaves, any remaining earlier graph node, or an integer from `-4` through `4`. Both operand orders and repetitions are allowed. Keep every other graph row and the output unchanged.

The 55 eligible `(n,c)` pairs and all candidate operand/operator tuples are enumerated. Distinct tuples can describe the same resulting graph. Any candidate has at most 78 operations after deleting `c`; some may have additional dead nodes. The search does **not** allow new larger constants, later or new intermediate nodes, other changes to the DAG, substitutions of witness variables, or changes to the output condition.

The certificate is a single explicit **counterexample input**, used to refute every identity in this finite class, not to infer an identity from testing. For the `j`th natural input in the pinned order, starting at `j=1`, set

```text
input[j] = 7919*j² + 1234567*j + 13579.
```

Evaluate the original and each candidate using the pinned P72 port integers, modulo `2305843009213693951 = 2^61 - 1`. The original output residue is `2118908950514353078`; every enumerated candidate has a different output residue. If any candidate's output were the identical integer polynomial at those ports, the two evaluations at this natural input would have to be equal as integers and hence equal modulo the displayed modulus. The observed modular inequality is therefore a rigorous counterexample to that candidate's universal output identity. Primality of the modulus is not used.

The checker pins the candidate JSON and all 79 corresponding Lean source rows and aliases, authenticates the four P72 gzip/raw hashes against the separately recorded P115 hashes, constructs the witness and exhausts the stated class. It caches the reevaluation of downstream descendants by their substituted modular value; no polynomial expansion or Lean run is involved. The P72-byte-to-Lean-port and physical PDF associations remain separate obligations.

This result does not show that a candidate has a different zero set: unequal output values can still define the same equation, for example after multiplication by a nonzero factor. It does not exclude a conditional identity on zeros, nonlocal refactoring, witness reparameterization, a different fixed-port expression, larger constants, a different cost metric, or any other reduction. No new equation, degree, consistency equivalence, or minimum is claimed. The underlying graph remains 14 variables, 79 operations and reported degree 107.

An [independent review](../../reviews/ordinary14-natural79-local-gate-obstruction-independent/README.md)
checks the class enumeration and the modular exclusion with a different
output-evaluation method.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-local-gate-obstruction/check.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-local-gate-obstruction/result.json
```
