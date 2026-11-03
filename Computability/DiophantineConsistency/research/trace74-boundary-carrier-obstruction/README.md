# Carrier divisibility obstruction for the q=2 boundary seed

For the finite partial-constraint seed in
[`trace74-boundary-seed-probe`](../trace74-boundary-seed-probe/README.md),
fix `h=beta*J=1`, `X=14`, `Y=8`, and `c=58563`. The exact trace74 rows give

```
D=X*Y=112,  H=4*(X*Y+Y)-1=479,
K=X*(3*c-2*X)+2=2459256,  M=h*D*H=53648.
```

For **every integer** choice of the remaining registers B,e,n,V, the pinned
rows give

```
Z = h*D*(H*(n-V²*B)+K) - H*(D*B+h*e),
Z mod H = h*D*K mod H = 176.
```

Since H divides M and this residue is nonzero, `M` cannot divide `Z` for
any such remaining register values. This is an exact algebraic obstruction
to completing the boundary seed with an **integral** `Z/M`; it does not prove
that the 74 equation has no zero at this seed, because no theorem here derives
`M | Z` from a 74 zero when the corresponding old alpha is zero. It is not a
counterexample, a fixed-port result, or a Lean formalization.

`check.py` pins the candidate JSON, checks the complete carrier-row shape,
and verifies the small integer values and residue. The universality in the
remaining registers follows from the displayed row identity and divisibility
by H, not from sampling. Run `python3 -I -S -B check.py`; the captured output
is `observation.txt`.
