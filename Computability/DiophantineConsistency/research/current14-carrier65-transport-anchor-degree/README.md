# A structural limit on direct transport-anchor aliases

This is an exact algebraic observation about **direct aliases**, not an
operation lower bound. It does not exhibit a smaller equation, prove a Lean
theorem, or bind any PDF. It considers all 58 `z`-free preaggregation gates
in the maintained graph.

Write `L=transport_partial` and `b=beta*J`. The pinned fixed port beta is
positive and `J` is an indeterminate, so `b` is a nonzero polynomial.
The transport factor is

```
Nt = L − b*z,
```

and `L` is independent of z. For any z-free polynomial `t` and any nonzero
integer polynomial `A`, possibly depending on z, the polynomial ring over
the actual fixed ports is an integral domain and

```
deg_z(t + A*(Nt−1)) = deg_z(A)+1 >= 1.
```

Such a shear cannot directly equal a z-free gate. The only z-dependent
preaggregation nodes are `zqm=b*z` and `Nt`. Comparing z-leading
coefficients and constant terms gives the two exact exceptional cases

```
t + A*(Nt−1) = Nt    iff A=1  and t=1,
t + A*(Nt−1) = zqm   iff A=−1 and t=L−1.
```

The checker pins the maintained graph and actual port payloads, verifies the
two z-dependent nodes and all 58 selected targets, and finds a nonzero
modular residue witness for each target's difference from both exceptional
z-free expressions. Therefore none of these targets can be sheared directly
to any original preaggregation node by a nonzero polynomial A. A modular
nonzero is used only to disprove a polynomial identity.

The result does not rule out reuse of final aggregation nodes, combined
shears, other anchors, non-polynomial coefficients, cheaper multi-gate
expressions, or different zero-preserving transformations. It does not claim
that every formal shear has an acyclic implementation or preserves the
zero set; the separate audited transport-anchor theorem has its own
hypotheses, including an unchanged transport factor.

```
python3 -I -S -B research/current14-carrier65-transport-anchor-degree/check.py > /tmp/transport-anchor-degree.json
cmp /tmp/transport-anchor-degree.json research/current14-carrier65-transport-anchor-degree/result.json
```

Independent external review is recorded in
`../../reviews/current14-carrier65-transport-anchor-degree-independent/`.
