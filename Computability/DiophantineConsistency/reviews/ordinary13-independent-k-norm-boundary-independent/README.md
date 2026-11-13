# Independent review: independent-k norm boundary

The proposed family is a valid partial counterexample: the two displayed
natural norm identities hold while `k<eta`, including at the compact-shaped
q. An independent dense-coefficient integer-polynomial calculation and the
actual candidate's q, X, Y, k, c, ell, and Delta row wiring were checked;
the original audit's receipt also reproduces.

For any integer q≥1, choose `J=1`, `beta=q−1`, `n_w=1`, `n_s=0`, `k=2`,
and `eta=2q⁴+4`. All these selected coordinates and beta are nonnegative.
Then `X=q`, `Y=q³`, `m=X*Y²`, and `eta−k=2q⁴+2>0`. With
`a=Y*(X+1)`, the candidate rows give `c=2*(a+2)` and
`Delta=(a+2)²−1`. Direct expansion yields both

```
(2*m+1)² = 1+m*(m+1)*2²,
(2*(a+2)²−1)² = 1+Delta*c².
```

The first expression is the first Pell recurrence step: for
`B=2*(m−1)+1`, `xcoord 1 B=B+2=2m+1` and `ycoord 1 B=1`. At the symbolic
compact beta, `q=beta+1=2^(67*8807)`; the review does not expand that
coefficient or authenticate external PDF bytes.

The cited eta/zeta early-index draft has both `13≤n` and `n≤k`, which are
incompatible with k=2. That theorem's own applicability to the **changed**
independent-k graph is not established here. The partial family has not been
extended to the graph's signed first and main roots, rank congruence/window,
strong factor or auxiliary factor. It is not a full graph zero, and it does
not show that another positive witness cannot satisfy `k≥eta` or that the
candidate's zero-equivalence fails.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-independent-k-norm-boundary-independent/check.py
```

The checker pins the inspected sources, independently expands the two
polynomial identities, checks graph rows and bounded natural-coordinate
controls, and compares the earlier receipt. It does not run Lean or prove a
graph theorem in arbitrary models.
