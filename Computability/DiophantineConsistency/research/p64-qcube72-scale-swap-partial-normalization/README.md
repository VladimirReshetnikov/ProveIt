# A partial scale swap and a full-witness rigidity obstruction

There is an explicit way to change the q residue class at the same compact
ports while preserving X and Y and solving transport, under strong divisibility
conditions. It is **not** a full 72-to-76 witness map. In fact, for an actual
fixed-port 72 zero with `3|q`, no positive 76Y zero at the same ports can
preserve all four values `X,Y,c,k`. The second statement is a
standard-integer deduction from separately checked Lean components; their
composition is not itself claimed as a checked Lean theorem. Neither
statement asserts that an actual source or target zero exists.

## Constructive scale and transport step

Use the fixed compact beta `beta=2^590069−1`, masks and arbitrary K. Suppose
source coordinates have

```
J=2, q=2beta+1,  w=(beta+1)u,  s=(beta+1)³t,
u>0, t>0,  beta ∤ (K+u).
```

The `t` here is a new scale parameter, not the graph's first-root coordinate.
Set

```
J'=1, q'=beta+1,  w'=u*q,  s'=q³*t.
```

All four new values are positive, and direct multiplication gives
`X'=w'q'=wq=X` and `Y'=q'³s'=q³s=Y`. Since `beta≡1 (mod 3)`,
`3|q` and `3∤q'`.

At the **same K**, let `A=K+w'` and write `A=beta*z'+r` with
`0≤r<beta`. Because `w'=u(2beta+1)`, the nondivisibility hypothesis gives
`r>0`; also `w'>2beta`, so `z'>0`. Define

```
C'=1, F'=r, alpha'=beta−r.
```

These are positive, `F'+alpha'+C'=q'`, and
`(K+w')C'=F'+z'(q'−1)`, so the target transport equation holds. Conversely,
if `beta|(K+u)`, then `beta|(K+w')`, and no positive target transport is
possible with `J'=1`: reducing transport modulo beta would force `beta|F'`,
while positivity of `F',alpha',C'` and `q'=beta+1` gives `0<F'<beta`.
This converse concerns the stated target q' and transport, not all possible
changes of q.

For a transformed **72** valuation, keeping k, eta, the first-root
coordinate and h preserves c, the first residual and the free-main residual;
keeping f and i as well preserves the strong residual, because X and Y are
unchanged. This does **not** automatically preserve the auxiliary norm or
produce an old-carrier gamma for the 76Y target: those depend on the target
rank R'. For
example, if f,i,y are kept, choosing a positive integer T' with
`c*T'−R'=c*T−R` preserves the auxiliary expression V; divisibility and
positivity of such a T' are additional conditions, and other auxiliary
witness changes are not excluded. The target old carrier additionally
requires `h+k=Y²*gamma+(R'+1)` with positive gamma.

## Rigidity if all norm coordinates are retained

Suppose instead that a source actual positive 72 zero has `3|q`, and a
positive 76Y zero exists at the same fixed compact ports with the same
`X,Y,c,k` (other target coordinates may differ). The checked
[forward construction](../p64-qcube72-free-main-candidate/README.md) changes
only coordinate 13 to make a positive 72 zero from the target 76Y zero; its
same-coordinate old-carrier equation is made explicit in the checked
[76Y q theorem](../p64-qcube76y-fixed-q-not-three-draft/README.md).

For each of the source and forwarded target 72 zeros, the checked
[fixed-compact ranked-main theorem](../p64-qcube72-fixed-compact-ranked-main-draft/README.md)
gives `ycoord R (XY+Y)=c`. Strict monotonicity of that ordinate forces the
ranks to be equal. The checked [main-index root theorem](../p64-qcube72-main-root-draft/README.md)
gives each free-carrier root together with its own main index and ordinate;
the same strict monotonicity identifies each such index with its checked rank.
The two carrier roots are therefore the same `xcoord R (XY+Y)`. Since
`H=4(XY+Y)+3>0`, the two free-carrier identities then force the h
coordinates to agree by cancellation. The forwarded target's old-carrier
identity therefore becomes `h+k=Y²*gamma+(R+1)` for the source. This
contradicts the checked [same-witness no-gamma theorem](../p64-qcube72-divisible-q-no-old-gamma-draft/README.md),
whose `3|q` hypothesis holds for the source.

Thus the partial swap above cannot be completed to a 76Y zero while all of
`X,Y,c,k` remain fixed. A different normalization must alter at least one of
those four values, or use a route outside this same-port hypothesis. This is
a conditional impossibility, not a claim that either zero exists or that the
existential reverse implication fails.

[`check.py`](check.py) verifies exact scale and transport identities in
28,136 small-integer cases and checks 844 blocked-residue cases. It pins the
Lean source dependencies but does not evaluate actual compact zeros or prove
the general argument. Run `python3 -I -S -B check.py`; output is retained in
[result.json](result.json). No Lean theorem for this composed rigidity is
claimed here.
