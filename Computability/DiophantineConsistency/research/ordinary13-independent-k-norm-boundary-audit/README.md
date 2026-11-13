# Independent-k child: a compact-shape norm boundary

The 84-row independent-k candidate has an open reverse-map condition `k≥eta`. The two natural Pell norms alone do **not** imply that inequality, even when q, X and Y have the exact compact-port shape. This is a partial arithmetic counterexample, not a full graph zero or an obstruction to an existential witness replacement.

Take any integer `q≥1` and set

```
J=1, beta=q-1, w=1, s=1,
X=q, Y=q³, k=2, eta=2q⁴+4,
a=Y*(X+1), c=eta+Y*k=2*(a+2),
Delta=3+4a+a², tau=2*X*Y²+1,
g=2*(a+2)²-1.
```

Then `eta>k`, but the exact identities

```
tau² = 1+(X*Y²)*(X*Y²+1)*k²
g²   = 1+Delta*c²
```

both hold. The second is the standard two-step Pell identity with `Delta=(a+2)²-1`; the first is its corresponding basic first-norm identity. In the candidate, these selected values correspond to `n_J=1`, `n_w=1`, `n_s=0`, `n_k=2` and `n_eta=2q⁴+4`. For the symbolic compact beta, `q=beta+1=2^(67*8807)`, so no gigantic value needs to be materialized.

This assignment has not been extended to the other coordinates and is **not claimed to zero the graph**. In particular, it does not provide the actual signed first or main roots, rank/window/congruence, the strong factor, or the direct auxiliary factor. Its first-norm ordinate is the basic k=2 solution and does not satisfy the separate early-index lower bound `n≥13`. Those constraints might rule it out; the child graph's `k≥eta` forcing or replacement-witness question is still open.

The pinned eta-natural exact-index draft accepts general natural eta in `c=eta+Y*k`, but its much stronger common-index, rank, strong and auxiliary hypotheses cannot be transferred to the changed graph merely from these two norm equalities. Its source and the child provider remain unelaborated.

The checker verifies the displayed two identities as exact integer polynomial identities in q and checks the candidate's q, X, Y, c and k row wiring. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-norm-boundary-audit/check.py | cmp - research/ordinary13-independent-k-norm-boundary-audit/receipt.json
```
