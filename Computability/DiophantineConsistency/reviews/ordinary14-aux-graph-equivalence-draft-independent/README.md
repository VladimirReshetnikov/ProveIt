# Independent source review: 78↔79 auxiliary-coordinate client

**Source review passes; not elaborated.** The proposed client updates only
slot 11 and keeps the first, main, strong and guard fields fixed. The graph
trees also show that the signed auxiliary center z and coefficient Q do not
depend on that slot. The old auxiliary residual is
`(z+ιu)²−Q·ιu((z+ιu)+z)−1`; the new residual is
`(ιy)²−Q((ιy)²−z²)−1`. These agree under `ιy=z+ιu` by an exact ring
identity, and the other four residuals agree structurally.

In the proposed 79→78 direction, Q and z bounds are obtained from the
starting 79 graph zero; the conditional auxiliary lemma supplies positive y
and the slot update preserves all other positive coordinates. The reverse
direction obtains its bounds from the starting **78** zero and constructs
positive u; it does not assume an old witness. Both directions retain the
explicit positive beta and port-cast premise. The natural-port specialization
matches `P72Root.cast_port` but does not authenticate compact44 bytes.

The checker pins the client and imported source drafts, compares exact
slot-normalized DAGs and dependencies for the four common fields, Q and z,
proves the auxiliary substitution in a sparse integer polynomial ring,
and compares the full output DAG after that cut. It replays the author,
graph-norm and auxiliary-root independent receipts. These are source and
external algebra checks only: Lean parsing, `rfl`, tactics, positivity,
casts, object/provider ancestry, and the arbitrary-model theorem remain
unverified. The 84↔85 and other parent bridges, iPRA endpoint and external
file semantics remain separate. No Lean process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-aux-graph-equivalence-draft-independent/check.py
```

Compare stdout with `result.json`.
