# Independent q² graph/formula binding review

The [graph-binding packet](../../research/p64-qcube75-q2-graph-binding/README.md)
was reviewed against its frozen source graph and symbolic-zero packet. Its
verifier correctly deletes the sole `q3` gate, replaces `Y=q3*s` by
`Y=q2*s`, checks the exact 75 remaining rows and liveness, and structurally
compares the 21 stated formulas using associativity and commutativity for
addition and multiplication while preserving subtraction order. Its retained
result was reproduced byte-for-byte without Lean.

A separate [`check.py`](check.py) independently verifies topological order,
unique row definitions and liveness, then evaluates the changed graph on 100
deterministic small tuples and compares its intermediate factors and output to
directly written formulas. It pins the 76Y source graph. These finite checks
are controls, not a universal algebraic proof; the reviewed structural
comparison covers all symbolic inputs. Neither check evaluates the enormous
symbolic witness or proves existential equivalence or an iPRA theorem.

Reviewed SHA-256: binding README
`8c48b659d2438db11499efef19005d7810839525b5b837a47482b6d459bd4af8`, checker
`fbfecaa596eaf82998e938a4c055d9629e60a77bd06ca1d6eb2a906cdc7394d1`, result
`8e33563cdea90f6e346ef1256a2a5f13a118b94b40164b413a6dd5cf0e77aaed`.
Run the independent check with `python3 -I -S -B check.py`.
