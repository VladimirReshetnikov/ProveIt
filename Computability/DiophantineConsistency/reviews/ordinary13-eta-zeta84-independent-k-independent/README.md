# Independent review: conditional independent-k 84-row candidate

The author receipt reproduces. The candidate has 13 nonnegative witness
coordinates, four unchanged integer ports and 84 topological binary
arithmetic rows. The independent check verifies every row and that every
input, port and row is live from the output. Its syntactic total-degree bound
is 110 with fixed ports; that is an upper bound, not an independently proved
exact degree or minimality statement.

In the 85-row parent, `n_zeta` appears only in
`kbase=n_eta+n_zeta`. The candidate deletes that row, renames coordinate 10
`n_k`, and replaces all uses of kbase with n_k. Therefore an arbitrary
parent natural valuation maps forward by setting `n_k=n_eta+n_zeta`, with all
other coordinates and ports unchanged; exact row-by-row substitution makes
the outputs equal. Conversely, a candidate valuation satisfying
`n_k≥n_eta` maps back by setting the parent's zeta coordinate to
`n_k−n_eta`. The subtraction is natural/model-natural truncated subtraction
only under this inequality, which ensures that the parent sum recovers n_k.
The 500 modular controls supplement rather than replace this structural
identity.

The inequality is an additional condition on the child valuation. A vector
with eta=1 and k=0 demonstrates the coordinate boundary, but is **not
claimed to be a graph zero**. Neither child-zero forcing of `k≥eta` nor an
alternative zero witness within that region has been established at compact
ports. Thus the justified statement is parent zero existence iff child zero
existence **with the inequality**, not an unrestricted compact equivalence
or an 84-operation equation proved equivalent to consistency. The parent
probe's own zero maps and parent endpoint remain unelaborated as well.

No Lean, provider, axiom, external consistency encoding or PDF binding was
checked. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-eta-zeta84-independent-k-independent/check.py | cmp - reviews/ordinary13-eta-zeta84-independent-k-independent/receipt.json
```
