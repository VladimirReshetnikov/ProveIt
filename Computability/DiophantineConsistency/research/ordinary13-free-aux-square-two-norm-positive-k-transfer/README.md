# Transfer of the two-norm k>0 argument to the free-y² graph

For the [84-row free auxiliary-square graph](../ordinary13-free-aux-square-compact-factor-obstruction/candidate.json), suppose all witness inputs and all four ports are ordinary nonnegative integers with

```
beta>0,  K0>0,  MC<beta,  MF<2*beta.
```

If A0=A1=0, then `k=eta+zeta>0`; consequently `c=eta+Yk>0`. An ordinary integer **full output zero** also supplies A0=A1=0 by the first/main factor-unit argument below. At the exact fixed symbolic compact tuple these port inequalities are the retained compact-source bounds. This is a standard-integer source/identity transfer, not a Lean model theorem, compiled provider/axiom audit, zero correspondence or iPRA endpoint.

The separate [independent-k two-norm proof](../ordinary13-independent-k-two-norm-kpositive-audit/README.md) derives k>0 under precisely those natural port inequalities and A0=A1=0. Its argument allows both signs of C and does not require the auxiliary square to be a square. The checker here reconstructs **exact ordered expression trees** for all first/main and rank fields of both 84-row graphs. Replacing the independent graph's `n_k` by `eta+zeta` makes the two A0 and A1 trees, and their relevant internal fields, identical. The free-y² input occurs in neither residual. Thus the two-norm arithmetic proof applies with no assumption eta≤an independent k and no use of the now-refuted independent-k zero correspondence.

At a full output zero the four integer factors multiply to one, so each is ±1. The exact first and main factor patterns are never −1 modulo four; the checker exhausts their respective 1,024 and 256 residue cases. They must therefore be +1 and A0=A1=0. Since Y=q³s>0 under natural ports and shifted s≥1, `k>0` entails `c=eta+Yk>0`. This excludes the c=0/m=0 case left open in the preceding [positive-index boundary](../ordinary13-free-aux-square-first-main-index-boundary/README.md), under its same compact port specialization. That boundary's q² conclusion still applies only to J=1, w=s=1.

The receipt reproduces both predecessor checkers, pins their sources, checks the exact first/main tree substitution and finite factor-residue exclusions, and inspects the compact bound declaration signatures. The quantified two-norm arithmetic is inherited from the pinned written proof; finite controls and source declarations do not constitute Lean replay, coherent provider selection, an axiom report or a PDF binding. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-aux-square-two-norm-positive-k-transfer/check.py | cmp - research/ordinary13-free-aux-square-two-norm-positive-k-transfer/receipt.json
```
