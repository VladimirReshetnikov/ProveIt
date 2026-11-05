# Independent review: 67/106 graph to captured Lean syntax

**PASS as an external structural comparison.** The independent
[checker](check.py) parsed the frozen 67-row JSON graph and the stage-078
`ModelCarrierSyntax.expressionAt106` source separately, building exact
hash-consed expression DAGs modulo only associativity and commutativity of
addition and multiplication. Subtraction remains ordered; powers 2 and 3
are expanded as repeated multiplication. It matched all 19 listed cuts and
the complete output, with all 14 witness indices and four port indices
checked. It independently confirmed that all 67 producers, witnesses and
ports are live and the operation counts are 38 multiplication, 16 addition
and 13 subtraction.

The checker verified all graph-pinned compressed and raw coefficient bytes,
and independently linked the retained stage-078 source hash and output
object hash to the direct syntax-provider record in stage 079; the referenced
object currently matches that hash. The author's changed-witness negative
control and our ordered-subtraction control passed. The author's checker
reran with observed exit 0 and byte-identical output. Our checker likewise
ran exit 0 and retained [result.json](result.json). The author's outer
observation records a separate exit 0; we did not witness its original run.
No Lean process was run in this review.

The comparison is external source/graph evidence, not a Lean theorem about
JSON or PDF output. Hashing the coefficient files against their metadata
does not independently prove their numerical equality to the actual current14
port tuple; that is a separate coefficient audit. The degree-106 certificate
was not rerun here. Stage-079's object has inherited historical provider,
package and dynamic ancestry; this review does not claim it is a coherent
fresh current14-base build or establish an internal iPRA endpoint on its own.

Independent checker SHA-256
`b5099442ab113f3aa0f7110a257f00cd852c8683f49a9dbba9f6cc92dae644b0`;
result SHA-256
`89fd90d14e16264bfd12a1489fbb8a03c9cf61c8e27adac9cfd904906a22094e`.
