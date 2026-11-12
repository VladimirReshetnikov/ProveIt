# Independent review: shifted-Pell natural-input graph

The [candidate](../../research/ordinary14-natural-shifted-pell83/README.md)
has 14 natural inputs, an explicit 83-operation graph, and exact degree 97 at
the externally authenticated P72/P115 ports. Its natural-zero existence
agrees with the natural-82 parent under the stated `beta>0`, `K0>=0`
hypotheses, with arbitrary integer `MC`, `MF`, conditional on the parent's
unit-factor result. This is a straight-line upper bound, not a minimum.

The first factor of the parent is `r²−ell*(ell+k)` and none of its other
gates use `r`. Substituting `r=ell+t` gives the new factor
`t²+ell*(2*t−k)`. Since `ell>0` under the stated assumptions and the other
natural inputs, any new zero yields a parent zero with natural `r`.
Conversely, the inherited unit-factor argument makes the first factor of any
parent zero equal one, which implies `r²=ell²+ell*k+1>ell²`; positive `ell`
and natural `r` then give `t=r−ell>0`. The coordinate changes are inverse
on zeros. This review relies on the parent unit-factor and negative-Pell
arguments; it does not replay their unbounded proofs in Lean.

The checker separately verifies the exact 82-to-83 graph edit, topology,
liveness and the formal factor identity. For the degree upper bound, it
compares the entire graph with the [positive 75-operation shifted-Pell
graph](../../research/ordinary14-shifted-pell75/README.md), where the
coordinate substitutions are the identity or an increment by one. It
checks each retained row after renaming and verifies the `qF`, `r0` and
guard cancellations as formal integer-polynomial identities. Thus the
natural graph inherits the positive graph's independently reviewed degree
upper bound 97. For the lower bound, it authenticates the actual port bytes
against both pinned bindings and obtains coefficient `979034495` of the
`t=2x`, other-inputs-`x` ray by a 97th finite difference modulo
1,000,000,007. This differs from the candidate's coefficient propagation.

The review does not establish an iPRA theorem, Lean elaboration, a binding
of the graph to the displayed PDF, provider coherence, or global
optimality. The source endpoint and the unbounded factor argument remain
inherited assumptions of this check.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary14-natural-shifted-pell83-independent/check.py | cmp - reviews/ordinary14-natural-shifted-pell83-independent/result.json
```
