# Short prefix fragments aligned to shared syntax

The manifest gives an acyclic DAG of 44 shared-node decompositions and five
row decompositions. Leaves are 29 separately included ASCII fragments, each at
most 32 bytes; operator tokens and references compose them. The author
[checker](check.py) verifies hashes, reference acyclicity and that materializing
the five rows reconstructs the independently audited prefix rows exactly. The
[independent external audit](../../reviews/nine-sharing-sign14-prefix-dag-fragments-independent/README.md) passed; the packet is frozen. This is an external byte check, not a
Lean theorem about the full original files or JSON. The intended Lean route is
to prove small fragment and shared-node encoding lemmas, then compose them
without one large normalization.
