# Natural-input 86-operation graph by exact shift cancellation

This **proposed external straight-line program** computes exactly the same
integer polynomial as the reviewed [natural 88-operation shift](../ordinary14-root74-natural-shift88/),
for every integer input and every integer port tuple. Its 14 intended inputs
are nonnegative integers, so it has the same natural zero set as that graph
and, via `x=n_x+1`, the same positive-zero existence as the reviewed
[74-operation positive-input parent](../ordinary14-positive-guard74/).

The 88 graph first computes `F=n_F+1` and `h=n_h+1`, and also has
`q=1+qm`. Those increments occur only in the displayed cuts. The two exact
integer-polynomial identities are

```
qF_old = (1+qm)−(n_F+1) = qm−n_F = qF_new

guard_old = g27+qF_old−qm*(n_h+1)
          = g27−n_F−qm*n_h = guard_new.
```

The new graph deletes the two `F` and `h` increment gates, computes
`qF=qm−n_F`, `guard_base=g27−n_F` and `bt_quotient=qm*n_h`, then uses the
same guard subtraction and all other rows as before. Its 86 operations and
all fourteen inputs and four ports are live. The checker verifies both cuts in
an exact sparse integer-polynomial ring, checks that F/h and the two differing
intermediates have no other old uses, and proves all remaining downstream
nodes match by structural congruence with the two established cuts. It also
checks 500 full-graph signed/natural cases; these controls are not the proof of
polynomial equality.

The 86 count is the size of the explicit graph, an **upper bound**, not a
claim of minimality. It does not show that Lean's `positiveShift` syntax has
86 operations or formally bind this JSON to that syntax.

## Specialized degree

At the externally authenticated P72/P115 fixed port bytes, exact total degree
is **107**. The upper bound is inherited from the replayed 88 graph's exact
main-factor cancellation certificate; exact polynomial equality transfers that
bound. The 86 graph itself, with all natural inputs set to `t`, has degree
107 and leading coefficient 419359493 modulo 1,000,000,007, proving the lower
bound. The checker independently reauthenticates P72 raw/gzip bytes against
the pinned P115 hashes before evaluating that ray.

These external graph and byte checks do not prove a Lean connection between
this JSON and the symbolic ports, a physical equation/PDF binding, an iPRA
endpoint, or global optimality. The root74 model and iPRA source proposals
remain unelaborated.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-natural-cancel86/check.py | cmp - research/ordinary14-root74-natural-cancel86/result.json
```

Independent external review: [natural cancellation 86](../../reviews/ordinary14-root74-natural-cancel86-independent/README.md).
