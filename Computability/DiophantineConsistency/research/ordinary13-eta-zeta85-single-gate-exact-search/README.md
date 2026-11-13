# Bounded one-gate identity search for the 85-row eta/zeta-natural graph

This packet records a **bounded obstruction**, not a new equation or a minimality proof. On the exact [85-row eta/zeta-natural probe](../ordinary13-eta85-zeta-zero-boundary-audit/probe.json), it searches for the following local circuit rewrite:

1. Choose an existing operation and one of its direct predecessor operation rows whose only consumer is that operation.
2. Replace the chosen operation by one binary `+`, `−`, or `*` operation on any two earlier available wires or integer constants 0 through 4, excluding the predecessor to be deleted.
3. Require the replacement to equal the original chosen gate as an integer polynomial in all witness and port variables. Deleting the now-unused predecessor would then save one row while preserving every downstream value.

There are 60 such operation/predecessor pairs and 1,099,002 replacement expressions in this stated search space. The checker rules out **every one** using eight explicit deterministic assignments modulo 1,000,003. For each expression at least one assignment differs from the original gate. This is a conclusive refutation of polynomial identity for those expressions: an integer polynomial identity would remain equal under every modular evaluation. The use of pseudorandomly generated assignments does not make that negative conclusion probabilistic; the finite counterevaluations are reproducible.

The result does not cover rewrites changing more than one remaining operation, different gates without an exclusive direct predecessor, other integer constants, reordered or new operations, fixed-compact-port-only polynomial identities, changed witness coordinates, or zero-set-only correspondences. In particular, the single-row independent-k coordinate candidate is not justified by this search: a separate [symbolic full child zero](../ordinary13-independent-k-fixedpoint-full-zero/README.md), with [independent review](../../reviews/ordinary13-independent-k-fixedpoint-full-zero-independent/README.md), shows its pointwise eta≤k forcing fails at the compact tuple. That counterexample does not settle an existential replacement map or the parent zero question.

No Lean execution, provider selection, internal proof, fixed equation or PDF semantics follows. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-eta-zeta85-single-gate-exact-search/check.py | cmp - research/ordinary13-eta-zeta85-single-gate-exact-search/receipt.json
```
