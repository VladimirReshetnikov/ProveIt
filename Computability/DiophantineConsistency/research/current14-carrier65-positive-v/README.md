# Positive auxiliary value at every positive zero

At every positive integer zero of the maintained 14-input equation, under
its usual fixed-port bounds, the literal auxiliary value

```
V = f²*(c*T−R)−c
```

is **strictly positive**. More precisely `c>2R>0` and `f²>c`. This is a
necessary condition, not a smaller equation or a new Lean theorem. The
argument is ordinary mathematics using the factor-unit and first-Pell
classification from `../carrier65-independent/PROOF.md`; its historical
provider and PDF boundaries remain as recorded there.

Assume positive inputs and ports with
`beta>=31`, `K>0`, `0<MC<beta<MF<2*beta`, and that the maintained scaled
polynomial is zero. Its independently reviewed unit argument gives
`N0=Nt=1` and `f²−Delta*(i*c²)²=1`. The transport equation forces
`C=q−F−alpha>0`: if `C<=0`, then

```
Nt=(K+w)*C+(q−F)−z*(q−1) <= (q−1)−z*(q−1) <= 0.
```

Put `u=q−F`. Then `2<=u<=q−1` and `1<=alpha<=u−1`, so the gap obeys
`2q−1 <= gap <= q²−q−1`. The mask term satisfies

```
0 < (MC+q*MF)*J < (1+2q)*(q−1).
```

Consequently the literal rank has `1<R<q⁴−q³`. Also
`E=X*Y=w*s*q⁴>=q⁴`, giving `1<R<E`. The first trace
`tau=E*n+k−R` is therefore positive.

Let `m=E*Y` and `P=2m+1`. Since `ell=m*k`, the first factor is
`tau²−m(m+1)k²=1`. The reviewed consecutive-product Pell classification
says that for an integer index `h>=1`,

```
tau=chi_P(h),   k=2*psi_P(h).
```

If `h=1`, then `tau=2EY+1` and `k=2`; the trace equation would make
`E` divide `R−1`, impossible because `1<R<E`. Therefore `h>=2` and

```
k >= 2*psi_P(2) = 4P = 8EY+4,
c = k*Y+eta > 8*E*Y² > 2R.
```

Finally `Delta=(a+2)²−1>=3`, and the strong unit equality implies
`f²=1+Delta*i²*c⁴>c`. Positive T gives `c*T−R>=1`, so

```
V >= f²−c > 0.
```

This uses the actual transport factor and the positive input n. It must not
be applied to a proposed encoding where those hypotheses have been removed;
in particular it does not by itself repair the separate 13-variable
transport-elimination argument or establish its completeness.

The checker pins the source gate rows and runs finite controls for the rank
polynomial identity and gap inequalities. Its `R=1` Pell control shows why
the strict lower bound is needed to exclude index 1. These finite checks do
not replace the unbounded unit and Pell arguments.

```
python3 -I -S -B research/current14-carrier65-positive-v/check.py > /tmp/carrier65-positive-v.json
cmp /tmp/carrier65-positive-v.json research/current14-carrier65-positive-v/result.json
```

Independent external review is recorded in
`../../reviews/current14-carrier65-positive-v-independent/`.
