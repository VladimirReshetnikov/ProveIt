# Natural-input 85-operation graph by zeta-shift cancellation

This proposed external straight-line program computes exactly the same integer
polynomial as the reviewed [natural 86-operation graph](../ordinary14-root74-natural-cancel86/)
for every integer input and every integer port tuple. Its 14 intended inputs
are nonnegative integers. Thus it has the same natural zero set as that graph
and, via the original positive shifts, the same positive-zero existence as the
reviewed 74-operation positive-input parent.

The old graph computes `zeta=n_zeta+1`, `k=eta+zeta`, `g52=k-R`, and
`r0=g52-1`. The new graph instead computes

```
kbase = eta+n_zeta
k     = kbase+1
r0    = kbase-R
```

The equalities `k_old=eta+(n_zeta+1)=k` and
`r0_old=(k_old-R)-1=kbase-R` hold over every commutative ring. The deleted
`zeta` and `g52` nodes have no other old uses; every remaining node agrees by
structural congruence once these two exact cuts are established. The checker
verifies the cuts as sparse integer polynomials, confirms the precise row
transformation and topological ordering, checks all 84 shared nodes, and
verifies that all 85 gates, all 14 inputs and all four ports are live. Signed
and natural full-graph controls supplement, but do not replace, that exact
identity argument.

The 85 count is the size of this explicit graph, an **upper bound**, not a
claim of minimality. No claim is made that Lean's `positiveShift` syntax has
85 operations or that this JSON is formally bound to it.

At the externally authenticated P72/P115 fixed port bytes, the graph has exact
total degree **107**. Its exact equality with the 86 graph transfers the degree
upper bound from the replayed 86 and 88 certificates. Evaluating the 85 graph
on the diagonal where every input is `t` gives degree 107 and leading
coefficient 419359493 modulo 1,000,000,007; the checker independently
reauthenticates the raw and gzip P72 bytes against the pinned P115 hashes.

These external graph and byte checks do not establish a Lean connection to
the symbolic ports, physical equation/PDF binding, an iPRA endpoint, or
optimality. The model and endpoint source proposals remain unelaborated.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-natural-cancel85/check.py | cmp - research/ordinary14-root74-natural-cancel85/result.json
```

Independent external review: [natural cancellation 85](../../reviews/ordinary14-root74-natural-cancel85-independent/README.md).
