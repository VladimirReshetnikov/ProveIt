# Independent audit: the offset-free conditional-separation merger

## Primary abstract theorem

Let `a0,a1,V0,V1,u,v,m` be integers. Assume

* `u>0` and `0<v/u<V0+V1`;
* `a0,a1>0`, `V0,V1>0`, and `a0<V0^2`, `a1<V1^2`;
* **conditional separation:** `m>0` implies `a0!=a1`.

For an integer `n>=0`, define

```
Omega=um,
Theta=un+v-Omega(V0+V1),
Phi(n)=(Theta^2-Omega^2(a0+a1))^2-4Omega^4 a0a1.
```

Then

```
(exists integer n>=0, Phi(n)=0)
    iff
(m>0 and a0,a1 are integer squares and u divides v).
```

The `Vi` must be positive, not merely satisfy `Vi^2>ai`. No unconditional
separation of the radicands is required. The quotient bound is used only for
completeness, not to prove a positive margin from a zero.

### Soundness: positivity before integrality

If `m=0`, then `Omega=0` and `Theta=un+v>0`, so `Phi(n)>0`.
For `m!=0`, put the rational number `s=Theta/Omega`. Over the reals,

```
(s^2-a0-a1)^2-4a0a1
 = (s-sqrt(a0)-sqrt(a1))(s-sqrt(a0)+sqrt(a1))
   (s+sqrt(a0)-sqrt(a1))(s+sqrt(a0)+sqrt(a1)).
```

Thus real numbers `r0,r1` exist with `ri^2=ai` and `s=r0+r1`. The strict
positive majorants give `ri>-Vi`. Therefore

```
Z=V0+V1+r0+r1>0,
n+v/u=mZ.
```

The left side is positive, so `m>0`, before any rationality of the individual
roots has been asserted. Conditional separation gives `a0!=a1`. Hence
`s!=0`, since a zero signed sum would give `r0=-r1` and `a0=a1`.
Now

```
r0=(s^2+a0-a1)/(2s),   r1=s-r0
```

makes both roots rational. A rational square root of an integer is an integer:
in a reduced fraction, the denominator squared divides the numerator squared,
so the denominator is one. Thus `Z` is an integer, and
`v/u=mZ-n` is an integer. This gives squarehood, divisibility, and the margin.

### Completeness: choose positive roots

Assume `m>0`, `u|v`, and let `ri` be the positive integer square roots of `ai`.
Set `Z=V0+V1+r0+r1` and `n=mZ-v/u`. Then `n` is an integer, and

```
n>=Z-v/u>V0+V1-v/u>0.
```

Substitution gives `Theta=Omega(r0+r1)` and makes one real factor vanish.
It is unnecessary to obtain a nonnegative `n` for every signed-root choice.

### Essential hypotheses

Without separation, take `a0=a1=2`, `V0=V1=2`, `u=v=2`, `m=1`, `n=3`.
The norm vanishes with `Theta=0`, although neither radicand is a square.
The positive margin must be used to exclude this zero signed sum.

Positive signs for the majorants are part of the theorem, not consequences
of squared inequalities. For example `a0=1,a1=4,V0=-2,V1=4,u=v=1,m=-1,n=0`
vanishes despite a negative margin. It satisfies the squared-majorant and
quotient inequalities, but not positive signs for both majorants.

### Earlier shifted version as a corollary

For provenance, apply the primary theorem with majorants `Vi+M` and
numerator `v+uM`. If `0<v/u<M`, its quotient bound holds because
`M+v/u<2M<2M+V0+V1`, and `u|(v+uM)` is equivalent to `u|v`. This gives
the earlier construction, which used
`Theta=u(n+M)+v-um(2M+V0+V1)`. Its soundness proof is the same real-factor
argument with `Z=2M+V0+V1+r0+r1>2M`. Once integrality is known, the equation
`n+M+v/u=mZ` gives divisibility. Conversely choosing integer roots and
`n=mZ-M-v/u` gives a nonnegative integer. It is valid but the concrete
register estimates below make both offsets unnecessary.

## Concrete conditional separation in the Jones registers

Use the ratio definitions in `nine/PROOF.md`. On every allowed outer
assignment, the source bounds imply `R,N>=8`, `b>0`, `Gcap>0`, all the
necessary tail registers are positive, and `A,C,J,D,E,F,G,H,P,K>1`.
In particular `V0=PK>0` and

```
V0^2-a0=K^2-1>0.
```

If

```
m=K^2 Gcap-4(C-KY)^2 Gcap-8gK^2>0,
```

then `g>=0` and `Gcap>0` yield `4(C-KY)^2<K^2`, hence
`|C-KY|<K/2`. Since `Y=N^2s>=64`, this implies
`C>K(Y-1/2)>K`.
Write `M0=RY`; then

```
A^2-P=M0^2((U+1)^2-2U)=M0^2(U^2+1)>0,
D-C^2=(A^2-2)C^2+1>0,
F-A^2=(A^2-1)(E^2-1)>=0,
G>=A,
I-G^2=(G^2-1)(H^2-1)>=0.
```

For `G>=A`, use `D>=A^2`, `C>=1`, and
`CD+1-A>=A^2+1-A>0` in `G=A+F(CD+1-A)`.
Consequently

```
a1=DFI>C^2 A^4>K^2 P^2>a0.
```

This proof uses neither squarehood nor divisibility. It therefore provides
conditional separation without circularity, also after replacing `a1` by
`64a1` in the merger.

## A sharper product majorant, including an extra independent refinement

Write `L=iJDC`, so `E=LC` and

```
F=(D-1)L^2+1.
```

Consequently

```
((2D-1)L)^2-4DF = L^2-4D.
```

Since `J>=3`, `D>=4`, `C>=1`, and `i>=1`, the right side is positive.
With `V1=(2D-1)L GH`, the radicand `4a1=4DFI` therefore has positive defect

```
V1^2-4a1=(L^2-4D)(GH)^2+4DF(H^2-1)>0.
```

An additional polynomial square-root truncation gives a lower-degree defect.
Put `k=iJC`, so `L=kD`, and define

```
T=k(8D^2-4D-1),
V1=TGH.
```

Direct expansion gives

```
T^2-64DF=(8D+1)k^2-64D.
```

Here `k^2>=9`, so the right side is at least `8D+9>0`. Also `T>0`.
Thus the radicand `64a1` has the strict positive majorant

```
V1^2-64a1=[(8D+1)k^2-64D](GH)^2+64DF(H^2-1)>0.
```

Apply the abstract theorem to `a0` and `64a1`. Conditional separation follows
from the already proved `m>0 => a1>a0>0`. An integer square root of `64a1`
is divisible by `8`, so its existence is equivalent to squarehood of `a1`.
The resulting norm is

```
(Theta^2-Omega^2(a0+64a1))^2-256Omega^4 a0a1.
```

This refinement was derived independently during the audit. It trades a
small increase in circuit size for a smaller exact polynomial degree;
whether it should be the primary presentation is a separate optimization
choice, not a correctness issue.

## Exact CRT reparameterization of the j witness

For the unchanged ratio definitions, `F=1 mod J` and `F=1 mod C` because
`E=iJDC^2`. Therefore `gcd(F,J)=1`, and

```
JF | (QF+J(H-C))
    iff
(J | Q and F | (H-C)).
```

The forward implication reduces the numerator modulo each factor, using
coprimality. For the converse, write `Q=Jq` and `H-C=Fz`, making the numerator
`JF(q+z)`.

In the original domain, `H=B1+jC`, `j>=1`, and `0<B1<C`.
If `F|(H-C)`, then `z=(H-C)/F` is a positive integer, and reduction modulo
`C` gives `z=B1 mod C`. Hence there is a unique integer `j'>=0` such that
`z=B1+j'C`: if `j'<0`, then `z<=B1-C<0`, a contradiction.
This proves the forward parameter transformation

```
H=C+F(B1+j'C),  j'>=0.
```

Conversely, for every `j'>=0`, this formula satisfies the original one with

```
j=1+((F-1)/C)B1+Fj'>=1.
```

It is an integer because `C|(F-1)`. The two transformations preserve the
actual value of `H`, not merely the square or margin predicates. Thus this
is a genuine bijection between the old divisible witnesses and the new
unconstrained `j'` witnesses, for fixed other coordinates.

After the transformation the only remaining divisibility is `J|Q`. The
primary, offset-free merger therefore uses `u=J`, `v=Q`. The strict quotient
bound follows from the concrete majorant estimate below. All positivity and
conditional separation arguments remain valid, because the new `H` equals an
old admissible `H` and also visibly satisfies `H>1`.
For positive coordinates encode `j'=j_positive-1`; for nonnegative coordinates
use `j'` directly. This domain change must be charged and stated explicitly.

## The concrete offset-free bound

Since `1<=W1<C`,

```
Q=3W1 C-2(W1^2-1) <= 3W1 C < 3C^2.
```

Also `D>C^2`, `D>=2`, `k>=1`, `G,H>=1`, and

```
8D^2-4D-1 > 3D.
```

Thus `V1=k(8D^2-4D-1)GH>3D>3C^2>Q>Q/J>0`.
In particular `v/u=Q/J<V0+V1`, exactly the abstract theorem's bound.
The final primary equation is therefore

```
Omega=Jm,
Theta=Jn+Q-Omega(V0+V1),
F9=(Theta^2-Omega^2(a0+64a1))^2-256Omega^4 a0a1=0.
```

Neither a separate `M` nor either former `Q` offset is needed. Completeness
chooses the positive square roots; there is no requirement that the witness
`n` be nonnegative for every possible signed-root choice.

## Scope

This is an ordinary mathematical proof and an independent algebraic audit,
not a newly kernel-checked formalization. The semantic compiler and Jones
ratio contracts remain imported dependencies. The proof does not establish
Con(ZFC), nor does it claim global optimality or a literature-first result.
