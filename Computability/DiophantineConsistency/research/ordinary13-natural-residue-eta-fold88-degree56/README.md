# Exact zeta/rank-offset fold: 13/88/56

This 13-natural-input graph has 88 live binary operations and exact degree 56
at the authenticated compact44 ports. It is **the identical polynomial for
all integer inputs and port tuples** as the pinned [89-operation parent](../ordinary13-natural-residue-forced89-degree56/).
Thus this source-level fold saves one operation without changing any zero,
variable or degree. This numerically improves the separately retained 13/88/60 natural graph at the same variable and operation counts, while the 13/87/60 graph uses one fewer operation at higher degree. These are comparisons of named constructions,
not a claim of global optimality.

The parent has `shift_eta=n_eta+1`, `shift_zeta=n_zeta+1`, and

```
k  = shift_eta + shift_zeta
g52 = k - R
r0 = g52 - 1.
```

The new graph replaces those uses by

```
kbase = shift_eta + n_zeta
k     = kbase + 1
r0    = kbase - R.
```

Both k and r0 are exactly equal to their old values over every commutative
ring. The deleted shift_zeta and g52 have no other uses, and all other rows
are unchanged. The checker verifies those identities in a free polynomial
ring, rowwise graph equality after the edit, topology/liveness and the parent
checker/receipt. Exact degree and the compact-port ray are inherited from
identical polynomial output, not inferred solely from syntactic degree.

The parent's positive-root and gamma arguments, its compact-port conditions,
and its standard-integer-only gamma/calibration boundary are unchanged. Its
model-level port-cast/zero-transfer and iPRA endpoint remain unelaborated, as
does a Lean identity for this new syntax. Compact44 is distinct from the
current-2011 displayed tuple. No external byte check proves PDF semantics.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-natural-residue-eta-fold88-degree56/build.py
python3 -I -S -B research/ordinary13-natural-residue-eta-fold88-degree56/check.py
```

The deterministic output is [receipt.json](receipt.json). The checker reruns
the pinned parent certificate but never invokes Lean.
