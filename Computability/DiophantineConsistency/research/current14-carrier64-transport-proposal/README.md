# Conditional 64-gate transport-coordinate proposal

This is a **conditional candidate**, not a proved reduction. It has 14
strictly positive integer inputs and 64 live binary operations with integer
leaves. Its positive-zero equivalence to the maintained equation is open.
The original displayed equation, its fixed ports, and its files are unchanged.

## Exact circuit change

Replace the positive input `alpha` by a positive input `C`. Keep every gate
except the following local change, with `q = beta*J+1`:

```
old: C = q-F-alpha; G = (q-1)*(q-F)+alpha
new:                 G = q*(q-F)-C
```

The two versions of `G` agree identically when `alpha=q-F-C`. The old C
gate disappears and the two G gates stay, saving one operation. The complete
literal candidate is [graph.json](graph.json), pinned to the maintained
current graph and its exact fixed-port binding. Its census is 37 products,
15 additions and 12 subtractions. All 64 gates, 14 inputs and four ports are
live. An exact sparse-polynomial check verifies the local identity; the
unchanged rest of the gate list propagates the identity to the whole output.
Two hundred modular full-graph comparisons are additional controls.

## What follows and what is missing

Every positive zero of the old graph maps to a positive zero of this graph:
the independently established old zero theorem gives `Nt=1`; if `C<=0`,
then `Nt <= (q-1)-z*(q-1) <= 0`, a contradiction. Keep all other inputs.

In the other direction, a positive candidate zero maps to an old positive
zero by the same coordinates **if `C<q-F`**: the recovered
`alpha=q-F-C` is then a positive integer. Proving this guard on all candidate
zeros, or finding another valid positive-witness normalization, would complete
the missing reverse implication. It is not established here. In particular,
this packet does not claim an iPRA endpoint, a global operation minimum, or
an actual full zero of either graph.

## Why transport and the usual rank bounds are insufficient

At the actual fixed ports, put

```
J=F=s=n=eta=zeta=1, q=beta+1, C=q,
w=1+(q-2)*K, z=2+q*K.
```

All these inputs are positive, `Nt=1`, and the recovered `alpha=-1`.
The candidate's `G=q(q-2)`. The checker reads and hash-verifies all four
current port payloads and verifies `1<R<q^4-q^3<E` as well as
`tau=E+2-R>4`. Thus neither transport nor the old rank-window/carrier
positivity estimates force the reverse guard. This assignment is **not** a
full counterexample: with `eta=zeta=1` its first norm is strictly negative,
whereas any full zero requires that factor to be 1. The remaining variables
are not asserted to satisfy the complete graph.

In fact this scalar assignment cannot extend to a full zero for *any* choice
of `n,eta,zeta`. The actual `beta` is odd and `MC` is even, so `q`, this gap,
and `R` are even; `E` is also even. The consecutive-product Pell lemma in
`../carrier65-independent/PROOF.md` shows that the first norm equal to 1
forces its second coordinate `k=eta+zeta` even, while that norm also forces
`tau` odd. But `tau=E*n+k-R` would then be even. Thus the example is only an
obstruction before using the full first norm, not a full-zero counterexample.

The same partial assignment cannot be repaired by choosing other positive old
`F,alpha` while preserving `q` and `R`. Indeed, for old positive coordinates
with `C>0`, write `b=q-1` and `u=q-F`; then `2<=u<=b` and
`1<=alpha<u`. The gap has the unique Euclidean decomposition
`G=b*u+alpha`. Here `G=q(q-2)=b²-1=(b-1)*b+(b-1)`, forcing
`u=alpha=b-1`, a contradiction. Fixed `q` and fixed ports make `R` injective
in `G`. This is still a partial-scalar obstruction, not a full-zero result.

## Transport and the first Pell norm can both hold outside the guard

There is a second fixed-port construction that also satisfies the *first*
norm. The actual `q=beta+1` is even. Set

```
J=F=s=1, C=q+1,
w=q/2+(q-2)*K, z=1+(q+2)/2+K*(q+1).
```

These are positive integers, `Nt=1`, and the recovered `alpha=-2`. Direct
integer checks at the current ports give an odd rank `R` and
`1<R<q^4-q^3<E`. Define `Y=q³`, `m=E*Y`, and `j=(R+1)/2`. Let `(x,k)` be
the coefficients of the positive Pell power

```
(2m+1 + 2*sqrt(m(m+1)))^j = x + k*sqrt(m(m+1)).
```

Its norm is 1, `k>=2`, and `x>k`. Since `E` divides `m`, induction gives
`x=1 (mod E)` and `k=2j=R+1 (mod E)`. Thus
`n=(x-k+R)/E` is a positive integer. Choose `eta=1`, `zeta=k-1`; then the
carrier has `tau=x` and the first norm is exactly
`x²-m(m+1)k²=1`. The checker verifies the actual scalar inequalities and
checks both norm preservation and the congruence induction as exact symbolic
polynomial identities. It does not expand the enormous Pell power.

This is a positive assignment to the scalar and first-norm coordinates at
the actual ports, with the reverse guard false. It is **not** a complete
candidate zero: the other norm factors and their inputs are not solved. It
shows that the reverse guard cannot be deduced merely from the transport,
rank bounds, carrier positivity and first Pell norm.

This second construction cannot be repaired into old positive scalar
coordinates while preserving `q`, `R`, and `w`. Let `b=q-1`; here
`G=b²-2=(b-1)b+(b-2)`. The unique admissible old representation therefore
has `F=2`, `alpha=b-2`, and `C=1`. For those values, `Nt=1` would require
`K+w=2 (mod b)`, but the chosen `w` gives `K+w=q/2 (mod b)`, different
from 2 because `b=beta>=31`. A reverse construction may still change other
coordinates, and the remaining norm equations have not been solved.

There is also a conditional obstruction to the same-coordinate inverse on
full zeros. Suppose an old positive zero has `F>d>=1` and
`(q-1) | d*(K+w+1)`. With `h=d*(K+w+1)/(q-1)`, change only

```
F' = F-d,   C' = C+q*d,   z' = z+d*(K+w)+h.
```

The candidate's gap and `Nt` are unchanged, so every other factor and the
full output stay unchanged. All new inputs are positive, but
`alpha'=q-F'-C'=alpha-d*(q-1)<0`: old positivity and `C>0` give
`alpha<=q-2`. The checker verifies the exact gap and transport-change
identities. This is conditional on an old zero satisfying the stated
divisibility; it does not construct one or rule out some different inverse.

The underlying coordinate idea and a related transport-only obstruction
were previously studied for a different 77-to-76 graph in
`../p64-qcube76-transport-candidate/` and
`../p64-qcube76-fixed-port-boundary/`. This packet applies and checks the
proposal against the present 65-gate graph and present complete ports.

Run the read-only check from the DiophantineConsistency directory:

```sh
python3 -I -S -B research/current14-carrier64-transport-proposal/check.py
```

The checker pins the maintained graph and authenticates raw and compressed
ports. It runs no Lean process, native proof replay, or PDF interpretation.
The independent external review is in
`../../reviews/current14-carrier64-transport-proposal-independent/`.
