# Independent review: zeta-zero full-graph boundary

The two stated witnesses independently evaluate to zero for the complete 85-row probe over the integers, with all 13 input coordinates nonnegative and eta=zeta=0. In order, the probe values `(q,Y)` are `(0,0)` and `(1,1)`; evaluating the parent graph at the same tuples gives 9 and 97. All intermediate rows are evaluated, including both residuals, the strong residual and the auxiliary factor.

The first witness uses beta=-1; the second uses beta=0, K0=-2 and MC=-1. Neither is a compact-port example: the pinned compact definition takes a natural tuple `![beta,K,low,beta+high]`, with beta fixed to the positive natural `2^(67*8807)-1`. These examples refute universal same-witness zeta positivity for unrestricted signed ports only. They do not establish a zero at compact ports, a failure of an existential map changing witnesses, a model-level obstruction, or an equation reduction.

The independent checker verifies every graph instruction under the substitution `probe.n_zeta = parent.n_zeta+1`. The key changes are parent `k=(eta+parent.n_zeta)+1 = eta+probe.n_zeta` and parent `r0=(eta+parent.n_zeta)-R = (eta+probe.n_zeta)-R-1`; the other rows match under the `k` to `kbase` rename. This is an exact structural forward identity, not a conclusion drawn from modular samples. The author receipt is also reproduced.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-eta85-zeta-zero-boundary-full-zero-independent/check.py | cmp - reviews/ordinary13-eta85-zeta-zero-boundary-full-zero-independent/receipt.json
```

This is a bounded source and exact-integer review. No Lean build, compact-port full-zero search, or endpoint proof is claimed.
