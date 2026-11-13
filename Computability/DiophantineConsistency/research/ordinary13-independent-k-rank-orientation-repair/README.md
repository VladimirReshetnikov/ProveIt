# Proposed rank equality orientation repair

This isolated unelaborated alternative preserves the original rank-representation source and its [independent review](../../reviews/ordinary13-independent-k-rank-representation-second-independent/README.md). It changes exactly the final `linear_combination h` to `linear_combination -h`, and changes the namespace and axiom-query names to keep both source alternatives distinct. The original signed-rank helper states `ι(rank)=signed`, whereas the proposed target states `signed=ι(rank)`; the sign change is the candidate correction for that orientation.

The checker reproduces the original receipt, pins both sources, and checks the exact delta. It does not elaborate either tactic or source, establish any mathematical/model theorem, select providers, run an axiom audit, or close other dependencies. Even after this repair, the k-positivity composition and endpoint remain source-only.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-independent-k-rank-orientation-repair/check.py | cmp - research/ordinary13-independent-k-rank-orientation-repair/receipt.json
```
