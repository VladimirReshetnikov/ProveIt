# Independent source and mathematics review: positive 81→83 gap

This bounded review covers `research/ordinary13-positive81-to83-model-gap-audit/`.
Its receipt reproduces. The independent checker pins the actual 81, 83, 80,
89, 88, 87, 86 and eta-natural 85 source graphs, checks their exact row
relations and coordinate substitutions, and runs finite companion/rank
controls. It also evaluates one fully specified scalar completion modulo a
prime and confirms that completion is not a graph zero. Reproduce from this
directory with `python3 -I -S -B check.py | cmp - receipt.json`. No Lean,
model-provider replay or end-to-end theorem is supplied.

The 81 and 83 graphs share the non-first residual rows; the two changed first
carrier leaves are `K0` versus `K0*q` and `F` versus `F*q`. With
`b=q−1`, `C=q−F−alpha`, `D=C*K0−F`,
`Bprime=C*(X+K0)−F` and `B=C*(X+K0*q)−F*q`, direct ring algebra gives
`B=Bprime+b*D`. Consequently, if `Z(P,r)=b*(ell+k+r−kP)−P`, then
`Z(B,r+(k*b+1)*D)=Z(Bprime,r)`. The latter r-expression is signed and need
not be a positive model natural; it is not by itself a positive-domain map.

For a target carrier P represented by a **positive model natural** with
`P=b*t`, `t>0`, a common first norm `tau²=1+ell*(ell+k)` and `tau>ell`,
the natural witness `r=k*(P−1)+t+(tau−ell)` is positive and yields
`Z(P,r)=b*tau`. The predecessors in this formula are legitimate only after
P≥1 and tau≥ell have been proved. Switching to this root is an existential
witness construction; norm extraction, the model-natural representation of
P and t, and preservation of the other residuals remain separate source
obligations.

For nonnegative K0, positive X and F, either carrier's positivity implies
`C>0`; write `A=C*X>0`. If `B=A+qD>0` and `q≥1`, then `Bprime=A+D>0`:
when D≥0 this follows from A>0, and when D≤0 it follows from `qD≤D`.
The opposite direction does not follow from these weak scalar facts alone.
With `X≥q²`, `C≥1`, `F≤q−2`, and `K0≥0`, the companion satisfies
`B≥q²−(q−2)q=2q>0`. The exact difference transfers divisibility by b,
but this argument does not establish the missing bound X≥q² from a graph
zero.

The scalar control in the audited packet has `q=47`, `C=1`, `Bprime=46`,
`B=0`, and `X=47<q²`, despite the listed positive/rank facts and
`b∣Bprime`. Our receipt checks a concrete positive-coordinate completion of
that scalar assignment has **nonzero** 81 output modulo 1,000,003. It is
therefore a partial control, not a full graph zero or a counterexample for
the selected compact beta/ports.

The 81 and 80 graphs have the same first 73 rows, and the exact 80→89
mixed-shift, 89→88→87→86→85 substitutions are independently checked. For
positive 81 coordinates, lowering the ten mixed-shift positions then applying
the four forward shifts yields

```
(J,F−1,alpha−1,f,i−1,T−1,w,s−1,r,eta,zeta−1,y,gamma).
```

The six predecessors exist by positivity. The eta-natural graph's two
`kbase`/`r0` folds then evaluate to `k=eta+zeta` and `r0=k−R−1`, so the
shared first/main/strong/auxiliary fields have the claimed values. In
particular, the main root is `U*(X+a*c)+H*(U*gamma+R+1−k)` with no
`X*Y*q` addition. A zero of the 81 sum of squares implies zero of the 80
product in an ordered difference ring, but that all-model source adapter and
its cast/field proofs remain to be checked; this row inspection does not
elaborate it or use `ForcedEta`.

Given `F,alpha≥1`, `C=q−F−alpha≥1`, q≥2 and nonnegative represented port
terms, `q−F≥2` and
`(q−F)*(q−1)+alpha≥2q−1≥q+1`. Hence the stated natural rank satisfies
`R≥(q+1)*(q²−1)≥q³≥q²`. If a coherent model client establishes the
**same-graph** `X=Exp.exp R`, the existing model `lt_exp R` source interface
then yields `X>R≥q²`. The reviewed local rank/window sources alone do not
supply that same-graph power identity. The early-index client gives only
`(2n)%q⁴=R+1`; the fact-level growth/projection clients also require the
exact index, the same first and main recurrence coordinates and oriented
no-extra-term balance. Neither the different residue-90 power client nor the
eta-zero contradiction supplies those facts automatically.

No mathematical mismatch was found in the inspected cuts. Positivity,
nonstandard-model casts/divisibility, exact-index extraction, source tactics,
parent endpoint, fixed byte/PDF binding and iPRA translation remain to be
proved and checked; the external scalar and ring controls do not settle them.
