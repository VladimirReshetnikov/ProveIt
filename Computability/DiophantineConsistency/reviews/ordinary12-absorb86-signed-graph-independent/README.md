# Independent 86-row signed-graph review

The external comparison confirms that the 86-row DAG deletes the three
89-row operations that compute `ell+k+r-k*Bt`, then uses a new independent
input for that expression. All 86 rows are live. The Lean graph's witness and
port slots, rows and output fields match that DAG. Its checked `first_eval`,
`main_eval` and `ordinary_eval` theorems preserve the three residuals under
the stated map in arbitrary commutative rings. Their printed axiom reports
contain only `propext`.

The independent check verifies the author source snapshot, output object,
logs, sampled resource guard, selected predecessor object hashes and
1,291-file base union, and reruns the external DAG and obstruction checks.
The obstruction gives a positive input with first residual zero and `Bt>0`
whose mapped witness is negative; the other residuals are nonzero. It does not
show a full-zero counterexample.

The signed-ring identity alone does not prove that positive zeros transport
forward, a reverse existence equivalence, a halt theorem, or an iPRA
endpoint. No independent Lean replay was made, and package-transitive,
dynamic and historical source-to-object ancestry remain inherited.
