# Auxiliary exclusion for one compact-window partial assignment

For the specific `a,c,g,R` in the [compact-window partial assignment](../p64-qcube72-compact-window-partial-obstruction/README.md),
**no positive choice of `f,i,T,y` can satisfy both `W=0` and `Na=1`**.
This strengthens that packet's observation that its particular choice
`T=y=1` fails. It holds only with those main-Pell coordinates and rank fixed;
it does not exclude other 72 witnesses or address actual compact44 ports,
positive-zero existence equivalence, or an iPRA endpoint.

The argument applies the existing generic Lean theorem
[`signed_half_index_of_facts`](../../Lean/DiophantineConsistency/AdaptiveGap85GenericSignedHalfIndex.lean)
mathematically to the standard integers. This is a source-level specialization
and independent review of its premises, **not a newly checked Lean client**.

## Premises

The fixed main data are `a=189`, `D=(a+1)(a+3)=36480`, and

```
(g,c)=(191,1)^m_D,   m=4020619,   R=41.
```

The power is the one in the linked partial packet. By the Pell recurrence,
`c=ycoord m a` and `g²=1+D c²`, with `m,c,g>0`. The previously certified
first/main ratio gives `c>27k`, and the first Pell recurrence gives
`k≥2·2446738`; hence `2R<c`. The stronger numerical rank-window inequalities
also hold: `24≤R` and `R+q³+q+1=72≤q⁴=81` for `q=3`.

Since `m≥6` and `ycoord` is increasing, the existing `y_six` identity gives

```
c ≥ ycoord 6 a = 32(a+2)D² + 32(a+2)D + 6(a+2) > (a+2)D².
```

For any positive `f,i,T,y`, set `I=i c²` and
`V=f²(Tc−R)−c` as integers. If the strong residual vanishes, then
`I²+D=D f²`. If the auxiliary residual is also zero at `Na=1`, then with
`z=absdiff(f² T c, f² R+c)=|V|` its equation becomes

```
I² z² + y² = 1 + I² y².
```

These are exactly the theorem's strong and auxiliary hypotheses, with
`rp=R`, `rn=0`, `d=g`, and its positive auxiliary variable equal to this
independent graph input `y`. The required signs, `0<R`, `m>0`, the half-window,
and the large-`c` bound have all been supplied above. The theorem therefore
concludes `m=absdiff R 0=R`, contradicting `4020619≠41`. The absolute value is
essential: no sign choice for `V` is assumed.

[`check.py`](check.py) pins the referenced theorem source, the `y_six` source,
and the earlier partial packet; reruns the latter's finite premises; checks
all stated small bounds and 500 finite signed-square identities. The finite
cases are controls, not a replacement for the universal theorem and the
argument above. Run with `python3 -I -S -B check.py`.
