# Adaptive carriers with a unit-product finalizer

This ordinary-mathematics research gives two additional points for strictly
positive integer unknowns:

| Unknowns | Live binary operations | Exact degree | Literal circuit |
|---:|---:|---:|---|
| 12 | **101** | **78** | [p12_adaptive_degree78.json](p12_adaptive_degree78.json) |
| 13 | **90** | **55** | [p13_product_degree55.json](p13_product_degree55.json) |

The twelve-variable point improves the inspected source69 point
102/82 in both arithmetic cost and degree. The thirteen-variable point
exchanges degree for two fewer operations than source73's 92/30. Source74's
twelve-variable 100/110 remains a distinct tradeoff. These are comparisons
with inspected constructions, not global minimality claims.

The arriving wave11 structural-round11 archive (SHA256
`83bccd59ab691f7076a36c2b03cf84f05f8f7b2c04490ede94c389c29ec2034d`)
independently supplies exactly the same twelve-variable polynomial and
101/78 point. No novelty or priority claim is made for this reconstruction.
The separate [ordinary-norm candidate](../ordinary-unit-products/README.md)
materializes a later manuscript's stronger 100/70 proposal; the 101/78
construction remains a useful normalized-strong-norm checkpoint.

All additions, subtractions and multiplications count once, including
squaring and multiplication by a numeral. Integer leaves and register reuse
are free. The literal division-free circuits contain no dead gates and use
all their unknowns and all four fixed ports. The counts do not measure bit
complexity or printed length.

No Lean file was edited or compiled for this research: formalization is
paused. The new algebraic reductions below are ordinary proofs. Their final
interpretation as refutation equations inherits the ordinary compact44
native compiler/calibration argument from the cited sources; this directory
does not provide an end-to-end Lean theorem or an object-language ZFC proof.

## Binding and shared carrier

Use **one whole compact44 tuple** `beta,K0,MC,MF`: `beta=2^590069-1`,
`K0=K`, and `MF=MF_source` is already shifted. Do not shift MF again.
The raw port hashes are recorded in [CHECKS.json](CHECKS.json), and agree
between source69's [binding](../../con-zfc-diophantine-forms/69-cones-pell/positive/native/ACTIVE_BINDING.json)
and source74's verification receipt. No ports from compact54 or another
instance are substituted.

For either construction, define the following polynomial abbreviations;
they are not additional unknowns. Take `m=3` for thirteen variables and
`m=6` for twelve:

```text
J=mj+1,       q=beta J+1,       C=q-F-alpha,
E=XY,        k=eta+zeta,       c=kY+eta,
a=E+Y,       H=4a+3,          Delta=a²+H=(a+2)²-1,
ell=EkY,     b0=X+ac,         W=(q-1)k+1,
M=q³(q-1),   Bt=(qK0+X)C-qF,
Z=M(ell+k+r)+(q-1)Y-q³W Bt,
A0=Z²-M²[ell(ell+k)+1],
R=[(q-1)(q-F)+alpha](q²-1)+(MC+q MF)J,
r0=k-R-1,   U=q²Y,
Dstar=U b0+H(U gamma+qE-r0),
A1=Dstar²-U²(1+Delta c²).
```

Products such as `qF` and `qE` mean multiplication. This is exactly
source73's adaptive carrier and source74's equivalent carrier `U=q(qY)`.
It uses the lower-degree shift `qE` in place of source69's `q⁴X`.
The independent checker compares the two literal carrier polynomials with
source73 under `j_old=2j` for the twelve-variable construction.

## Thirteen positive variables, 90 operations, degree 55

The unknowns are

```text
j,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma > 0.
```

Using the shared carrier with `m=3`, put

```text
rho=f²-1,       Q=Delta rho,      I=ic²,
V=f²(cT-R)-c,   y=V+u,
F0=1+A0,        F1=1+A1,
Fa=Q V²+(1-Q)y²,                 Fs=f²-Delta I².

P13=F0 F1 Fa Fs-1=0.
```

The literal circuit evaluates `Fa=y²-Q(y²-V²)` to share the two squares.
This is the same integer polynomial.

**Exact local equivalence.** For every integer assignment to all the input
symbols and ports, `P13=0` if and only if all four residuals of source73's
thirteen-variable sum of squares vanish. In particular the positive zero
sets are exactly equal; this statement does not depend on native calibration.

Indeed, an integer product equal to one has only factors `+1` or `-1`.
Each of these four factors is never `-1`:

* `M=q³(q-1)` is even, so `F0` is `1+Z²` modulo four.
* `Delta=a²+4a+3` is zero or three modulo four. Thus
  `1+Delta c²` is zero or one modulo four, and
  `Dstar²-U²(1+Delta c²)` cannot be two modulo four. Hence `F1` is not
  three modulo four.
* `Q=Delta(f²-1)` is zero or one modulo four. Accordingly `Fa` is
  `y²` or `V²` modulo four.
* `Fs=f²-Delta I²` is zero, one, or two modulo four.

All factors must therefore be `+1`. Their equations are precisely
`A0=A1=0`, `Aa=Fa-1=0` and `As=Fs-1=0`, because
`y²-V²=u(2V+u)`. The converse is immediate. Composing this local identity
with source73's inherited ordinary proof preserves its refutation-existence
interpretation. The finalizer uses four factors directly, avoiding the
four residual squares.

## Twelve positive variables, 101 operations, degree 78

The unknowns are

```text
j,F,alpha,t,T,X,Y,r,eta,zeta,n,gamma > 0.
```

Use the shared carrier with `m=6`, and define

```text
f=t+1,       rho=f²-1,       d=Delta c⁴,       Q=Delta rho,
V=f²(cT-R)-c,
h(x)=(1-Q)x²+2(1-Q)Vx+V²-1,
bn=2(1-Q)(n+V),
AN=d h(n)+(1-Q)rho,
N=AN²-d bn² rho.

P12=(1+A0)(1+A1)(1+N)-1=0.
```

The literal circuit writes `h(n)=(V+n)²-Q[(V+n)²-V²]-1` and uses fixed
nonnegative powers only. There is no division or rational unknown in this
polynomial. The following proof-only rational coordinates explain its
equivalence.

### Rational-integrality lemma

If `Q>1` and `V` are integers, `y` is rational, and
`QV²-(Q-1)y²=1`, then `y` is an integer.

Changing signs permits `V,y>0`; a zero coordinate is impossible. Write
`y=a/b` in lowest terms with `b>0`. Then `b²` divides `Q-1`, so `b`
divides `Q-1`. For `V=1`, the equation gives `y=1`. For `V>1`, put

```text
V'=(2Q-1)V-2(Q-1)y,
y'=(2Q-1)y-2QV.
```

The first number is integral and direct expansion preserves the norm.
The original equation gives `y>V` and `QV>(Q-1)y`, hence
`-V<V'<V`. Its norm excludes `V'=0`. The reduced denominator of `y'`
is still `b`, since `2Q-1=1 (mod b)`. Taking absolute values and applying
strong induction on the positive integer `V` reaches `V=1` without
changing that denominator. Therefore `b=1`.

This is source69's descent, included here to make the integrality step
explicit. A resultant equation alone would give rational rather than
integral eliminated coordinates.

### Soundness and recovery order

Here beta and `J=6j+1` are odd, so `q` is even. Thus `M` and `U` are
even, `A0` and `A1` are squares modulo four, and `N` is a square modulo
four because `bn` is even. None of the factors `1+A0,1+A1,1+N` can be
`-1`. Consequently

```text
P12=0  <=>  A0=A1=N=0
```

on the stated positive domain.

Before using `N`, the carrier-only part of
[source74's proof](../../con-zfc-diophantine-forms/74-centered-pell-gaps/positive13/PROOF.md)
supplies the following consequences of `A0=A1=0`. The order avoids a
dependence on the eliminated strong or auxiliary equations:

1. Rational-square-root integrality gives `M|Z`. Reducing modulo `q³`
   and `q-1` gives `q³|Y` and `q-1|Bt`. Put `s=Y/q³>0` and
   `b=Bt/(q-1)`. With `tau=Z/M`,
   `tau=ell+k+r+s-Wb` and `|tau|<ell+k`, so `Bt>0` and then `C>0`.
2. The authentic whole-tuple mask bounds yield
   `q>=16` and `3q<R<q⁴-2`. The residue `J=1 (mod 3)` yields
   `q=2 (mod 3)`. Since `q³|Y`, one has `gcd(q,H)=1`.
3. `U=q²Y>=q⁵`, so
   `Dstar>Uac-Hk>k(UaY-H)>0`. Thus `A1=0` gives a positive main Pell
   root `D=Dstar/U` with `D²-Delta c²=1`.
4. The first and main Pell classifications give indices `n0,p>=1`
   with `k=2 psi_(2XY²+1)(n0)` and `c=psi_(a+2)(p)`. The case
   `n0=1` would give `k=2`, `eta=zeta=1` and `c=2Y+1`, contradicting
   `c>=2(a+2)>=4Y+4`. Therefore
   `c>kY>8XY³>=8q⁹>2R`.

Since `f=t+1>=2` and `T>=1`, the last bound gives
`V=f²(cT-R)-c>c>1`. Also `d>0`, `rho>0`, `Q>1`, and `bn!=0`.
At `N=0` define proof-only rationals

```text
i0=AN/(d bn),        u0=n-i0.
```

Then `d i0²=rho`. The defining identity for `AN` gives
`h(n)+(1-Q)i0²=bn i0`, hence `h(u0)=0`. Writing `y=V+u0` turns this
into `QV²-(Q-1)y²=1`. The lemma shows `y` is integral. Consequently
`u0=y-V` and `i0=n-u0` are integers too.

Take `i_positive=|i0|>0` and `u_positive=|y|-V`. Since
`(Q-1)(y²-V²)=V²-1>0`, the latter is positive. They satisfy

```text
f²-Delta(i_positive c²)²=1,
Q V²-(Q-1)(V+u_positive)²=1.
```

Together with the carrier equations these are exactly source73/source74's
four thirteen-variable residual equations, with its old coordinate
`j_old=2j`. All recovered coordinates are positive. That source's remaining
rank recovery restores `q|X`, its transport quotients and its normalized
compiler witness. In particular its transport convention is
`z_old=z_new+1`; the whole tuple and this convention have not changed.
Its ordinary native/K215 calibration then yields a finite syntactic ZFC
refutation. The calibration is inherited, not discharged by our finite
tests or by a newly supplied semantic hypothesis.

### Completeness

The canonical compact44 refutation witnesses used by source69/source74
have `B_native=2^590069`, `q=B_native^s`, and
`J=1+B_native+...+B_native^(s-1)` with odd `s>1`. Thus `J` is odd and
`J=1 (mod 3)`, so `j=(J-1)/6` is a positive integer. This restriction
is imposed only on these canonical completeness witnesses; we do not claim
that every thirteen-variable solution has even `j_old`.

Use source74's adaptive positive `gamma` and its canonical positive
strong/auxiliary witnesses `f,i,u,T`. The normalized strong equation makes
`f>1`. Set `t=f-1>0` and `n=i+u>0`, retaining all other coordinates.
Then `rho=d i²` and `h(u)=0`. The exact identity

```text
N |_(rho=d i²) = d² h(n-i)h(n+i)
```

gives `N=0`, while the two carrier residuals already vanish. Hence
`P12=0`. No new congruence on `f` and no new choice of auxiliary Pell pair
is required. This proves both existence implications after composing with
the same inherited ordinary compiler/calibration theorem. Negating gives
the corresponding ordinary equivalence with its syntactic `Con(ZFC)`.
An end-to-end Lean proof and an internal ZFC derivation remain separate
obligations.

## Exact degrees on the actual coefficient slice

Give every unknown degree one and each fixed port degree zero. In either
construction put

```text
q0=m beta j, k0=eta+zeta, c0=k0Y, Delta0=X²Y²,
R0=q0³(q0-F), Bt0=(K0q0+X)(q0-F-alpha)-q0F.
```

Writing `Z=M ell+e` gives the exact cancellation

```text
A0=e²+M ell(2e-Mk)-M².
```

Its degree is at most 15. If `z=U gamma+qE-r0`, the other exact
cancellation is

```text
A1=U²(2acX+X²-Hc²-1)+2U(ac+X)Hz+H²z².
```

This has degree at most 13. Their highest homogeneous parts are

```text
L0=-2q0⁸k0²XY²Bt0,
L1=8q0²k0X²Y⁴(q0²Y gamma+R0).
```

For thirteen variables the other two factors have leaders
`La=2Delta0 f⁴uR0` of degree 13 and `Ls=-Delta0 i²c0⁴` of degree 14.
Their product with `L0 L1` has degree 55. Its monomial

```text
j¹⁵ eta⁷ X⁸ Y¹⁵ f⁴ i² u gamma F alpha
```

has coefficient `32(3 beta)^15>0`, independently of `K0,MC,MF`.
Thus specializing the authentic coefficient tuple cannot lower the degree.

For twelve variables, `deg(d)=12`, `deg(rho)=2`, `deg(Q)=6`,
`deg(V)=6`, `deg(h(n))<=13`, and `deg(bn)<=12`. Hence
`deg(AN)<=25`, while `deg(d bn² rho)<=38`. The degree-50 leader is

```text
LN=4Delta0⁴c0⁸t⁸R0²n².
```

The degree-78 product `L0 L1 LN` contains

```text
j¹⁸ eta¹¹ X¹² Y²³ t⁸ n² gamma F² alpha
```

with coefficient `64(6 beta)^18>0`, again independently of the other
three ports. These coefficients establish exact degrees 55 and 78.
The checker expands the displayed homogeneous forms exactly and checks
their selected coefficients. It also independently evaluates each complete
circuit in the univariate polynomial ring by assigning every unknown the
same indeterminate; the resulting degrees are 55 and 78.

## Reproduction and limits of the checks

With Python 3 and SymPy installed, run from this directory:

```sh
python3 build.py
python3 check.py
python3 -O check.py
```

[build.py](build.py) emits literal circuits and pins the source bytes;
[check.py](check.py) never imports it or executes source-package code.
The latter checks topology, exact counts and operation types, liveness of
every gate/input, all 768 relevant modulo-four cases, exact cancellation
and merger identities, literal carrier compatibility, exact homogeneous
coefficients and univariate degrees, 240 independent scalar-specification
comparisons, and the whole four-port binding. Checks use explicit failures
and remain enabled under `-O`.

The universal descent and witness reconstruction are the ordinary proofs
above, not consequences of bounded sampling. The tests neither prove
consistency nor execute a contradiction search. [SOURCE_PINS.json](SOURCE_PINS.json)
identifies the precise sources used, and [CHECKS.json](CHECKS.json) records
the generated-circuit hashes and finite results.
