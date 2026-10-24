# Independent audit: the H1868 positive prefix and degree 999,518

This note combines an exact finite algebra audit with an ordinary mathematical
proof of the positive-domain threshold calibration and the exact degree. It
does not replace the inherited source-calculus/native-compiler calibration.
The standalone script `audit_h1868_degree.py` uses only Python's standard
library and imports no producer or earlier checker.

## 1. Exactly which source is reused

The inherited H1868 data is the incoming round-11 `packing/certified` source,
also copied into that packet's `lucas_h1868/data`. The stored source is named
`gapN86`, with 31 positive coordinates and 22 quadratic equations. Its
coordinate substitutions are `P_old=P+eta+zeta`, `N_old=N+1`; its invertible
row changes are `rho14=r14+r2`, `rho15=r15+r3`. This is not a license to
substitute the old package-71 source verbatim. The new polynomial must retain
the exact H1868 source and its coherent original31 coefficient tuple.

The source tables have 31 distinct positive weights, maximum `W=116`, and
22 distinct targets, maximum `Q=1836`. The three kernel degrees are
`(1408,1727,1636)`, with leading coefficients `(-6,2,1)`. Thus the total
convolution height is `H=1868`, and the target headroom is `H-Q=32`.
There are 81 stored coefficient positions. The independent audit checks all
20,466 convolution interactions and every monomial, including absent ones,
in the 22 identities

```
[T^q_j] (D2(T) U_p(T)^2 + D1(T) U_p(T) + D0(T)) = 2 rho_j(p).
```

It also checks that every fixed kernel coefficient has absolute value below
`Mcoef=2^2134927` using the original31 port bit bounds, and that row 5 at the
all-one source tuple is exactly 1 independently of the coefficient ports.

## 2. Positive-domain prefix; the factor 2 is essential

Let

```
kappa=2134939,       B=2^kappa b^2,
ell=sum B^w_i,       Targets=sum B^q_j,
Us=ell+g,            Gs=(D2(B)Us+D1(B))Us+D0(B),
N0=B^117,            mask=N0-1-(b-1)ell,
Sc=g+N0(2Gs+Targets),
Tc=mask+N0(B-2)Targets,
L=2 b B^1986,
R=L(Sc+Tc+1)-Sc-1,
N=2^16012032 B^1055,
cap=b B^116.
```

All expressions are polynomials with fixed integer coefficients. In
particular `N` has no additional factor of `b`. The displayed factor 2 in
`L` and the absence of that factor of `b` in `N` follow from parity; they
cannot be copied from H1873 without recalculation.

The quadratic leading term dominates the linear one by 25 powers of `B`
and the constant one by 460 powers. Since `B>=4096 Mcoef b^2` and
`Us>=B^116`, the ordinary geometric-series estimates imply `Gs>0` on every
positive `b,g`, before any digit argument. The low mask is nonnegative, so
`Sc,Tc>=0`. The identity

```
R=(L-1)(Sc+Tc+1)+Tc
```

then proves `R>=8` and `R>=b` unconditionally; `N>=8` and `N>=b` are
immediate as well.

On the recovered ratio range `g<4cap`, one has `Us<6b B^116`. With
`Zbig=B^1869`, the bounds give

```
2Gs/Zbig < 86 Mcoef b^2/(B-1) < 1/32.
```

Both the target mask and its multiple by `B-2` use only positions at most
1837. Also `g<N0` and `mask<N0`. Consequently

```
Sc+Tc < N0 Zbig = B^1986 < L.
```

The same signed-carry argument as the inherited source applies. In a binary
base, disjointness against the low mask gives
`g=sum z_i B^w_i`, `0<=z_i<b`; then `p_i=z_i+1` are positive source
coordinates. Every convolution coefficient has magnitude at most
`993 Mcoef b^2 < B/4`. Sparse target correction by `+1` therefore accepts
exactly the zero target residuals. This uses the already-identified
signed-carry lemma, with unchanged coefficient and target-gap hypotheses.

Conversely a fixed positive source zero can be packed for all sufficiently
large powers of two `b`. Since the all-one tuple is not a zero, its packed
`g` is positive; the coordinate bound yields `g<cap`, the stronger bound
needed by ratio completeness.

## 3. Exact population threshold

Suppose `b=2^k`. Put `v=kappa+2k`, so `B=2^v`, and write `L=2^u`.
The low mask has 117 radix-B digits; at 31 distinguished positions its digit
is `B-b`, and at every other position it is `B-1`. Thus

```
pop(mask)=117v-31k.
```

The upper mask has 22 digits equal to `B-2`, each with `v-1` binary ones.
The blocks are disjoint, so

```
pop(Tc)=139v-31k-22.
```

As `Sc+Tc<L`, the two-block form of `R` gives

```
pop(R)=u+pop(Tc)-tau,
tau=pop(Sc)+pop(Tc)-pop(Sc+Tc)>=0.
```

The defect `tau` vanishes exactly when `Sc` and `Tc` are bitwise disjoint.
For the displayed exponents,

```
u=1+k+1986v,
u+pop(Tc)=2125 kappa+4210k-21,
2 log2 N=2*16012032+2110(kappa+2k)
        =2125 kappa+4210k-21.
```

The last equality uses `15*kappa-21=32024064`. Legendre's identity
`v2(binomial(2R,R))=pop(R)` therefore yields exactly

```
N^2 divides binomial(2R,R)  iff  Sc AND Tc = 0.
```

This includes `b=1`. At that value, however, the low mask is `N0-1`, so
disjointness and `0<g<N0` are incompatible. No exceptional endpoint is
silently accepted.

## 4. The complete-radical majorant certificate

Use the saturated local definitions

```
J=4A-5,       D=(A^2-1)C^2+1,
r=iJC^2,     F=(A^2-1)D r^2+1,
G=A+F(CD+1-A), H=C+FZ, I=(G^2-1)H^2+1,
a1raw=D F I, sigma=1024 C^5 i,
```

where the final composition sets `Z=B1+(j-1)C`. Let `Pplus` be the literal
333-term integer polynomial in `data/saturated_corrected_P.json`. The
independent checker reconstructs `a1raw` from the formulas, multiplies out

```
defect=Pplus^2-sigma^2 a1raw,
```

and verifies exact equality after `A=x+3,C=y+1,i=u+1,Z=v+1` with the
36,309-term certificate. Every displayed nonzero coefficient is positive,
and its constant term is `8341416066461366340`. Separately, translating
`Pplus` by `A=x+3,C=y+1` gives strictly positive coefficients and a
positive constant. Hence, for `A>=3,C,i,Z>=1`,

```
Pplus > sigma sqrt(a1raw) > 0.
```

This is a universal exact polynomial certificate, not an asymptotic claim.
Its derivation by a Laurent expansion is not a correctness premise once
the complete coefficient tables and their exact identity have been checked.

In the finalizer, take `a1=sigma^2 a1raw` and `V1=Pplus`. The proof in
`FULL_NINE_SOUNDNESS.md` applies with these substitutions. Dividing the
recovered integral root of `a1` by the positive integer `sigma` gives a
rational root of the integer `a1raw`, so that root is integral too. The
square certificate and saturated ProductPell theorem therefore remain
available. The completeness integer `n` remains positive because
`sqrt(a1raw)>4D` unconditionally: `F>3D`, `G>=3`, `H>=2` give
`I>=33` and hence `a1raw>99D^2`. Thus `Pplus>4D`.

## 5. Exact degree, with every dominant term identified

Under a simultaneous scaling of the nine input variables, the source has
positive leading terms

```
R ~ 4 b B^3971,      N=2^16012032 B^1055.
```

Therefore write

```
rR=deg R=7943,    nu=deg N=2110,
a=deg A=rR+4nu+2=16385.
```

The local polynomial's unique weighted leading terms, for weights
`(a,1,1,rR)` on `(A,C,i,Z)`, are

```
Pplus: 1048576 A^18 C^24 i^6 Z,
defect: 624687054848 A^18 C^48 i^12 Z^2.
```

Hence

```
deg V1=18a+rR+30=302903,
deg delta1=deg(V1^2-a1)=18a+2rR+60=310876.
```

Both leading coefficients are positive. The remaining exact degrees are

```
deg Omega=5a+2W+3,
deg E0=a+4,
deg V0=3a+rR+1,
deg delta0=deg(V0^2-a0)=3a+rR+2,
deg a0=2 deg V0.
```

Define

```
Bsmall=E0^2-2E0 Omega(V0+V1)+Omega^2(delta0+delta1).
```

Its unique highest-degree contribution is `Omega^2 delta1`, with positive
leading coefficient. The exact cancellation-resolved norm identity is

```
P9=Bsmall^2+4Omega^2 V0V1 Bsmall
       +4Omega^4(delta0 V1^2+a0 delta1).
```

The four displayed contribution degrees, respectively, are

```
950392, 999518, 991546, 753714.
```

Only the second is maximal, and its leading coefficient is positive.
Consequently the degree is exactly

```
59a+4rR+8W+103 = 999518.
```

This proves both the upper bound and its attainment for the actual positive
fixed coefficients. A degree computed only by propagating maxima through the
unresolved norm would miss the cancellations and would not prove this result.

## 6. Scope of the result

The independent executable audit passes all 22 source identities, all
20,466 convolution interactions, the coefficient bound, the exact positive
population-threshold parameters, the complete radical identity, coefficient
positivity, and the exact leading-degree comparison. It does not execute the
producer. The primary circuit's full transcription and operation count have
their own separate checker; this audit does not infer them from metadata.

The degree-999,518 polynomial improves the inspected nine-positive degree
frontier, while using a larger evaluator than the simpler saturated
majorant. It does not claim global minimality or historical priority for
norm saturation, which already appears in the incoming ten-integer work.
