# A full signed-fold toy zero outside the scalar-repair window

There is a **positive zero of all four residuals** of the sign-reversed 86/26
candidate for fixed integer ports

```
beta = 31, K0 = 9, MC = −31699, MF = 46,
```

at which `Bt<0` and the nonnegative scalar-shift repair criterion in
`../ordinary13-folded-root86-negated-shift-repair/` fails. This is a full
symbolic zero, not merely a partial scalar control. It uses a **negative toy
port MC**, not the actual compact44 numerals; it does not settle whether the
criterion holds at those actual ports, establish an unrestricted failure of
positive zero-existence equivalence, or give any Lean/iPRA theorem. This
packet is submitted for independent review.

## Exact witness

Take the full positive toy-parent tuple defined symbolically in the
independently reviewed `../ordinary13-folded-root86-toy-full-zero/` and retain
all of its inputs and original ports except as follows. Put `alpha=45` in
place of `14`, and `MC=−31699` in place of `14`. The toy tuple has

```
J=1, beta=31, q=32, F=1, K0=9, MF=46, R=998911,
X=2^R, b=J*beta=31,
Y=q³*s, ell=X*Y²*k, k=eta+zeta,
tau²=1+X*Y²*(X*Y²+1)*k², tau>0.
```

The positive integer definitions of `s`, `eta`, `zeta`, `f`, `i`, `T`,
`u`, and `gamma` and proof of their other three zero residuals are exactly
those in the reviewed source; they are not expanded as decimal integers.
Set the signed-fold first input to

```
C = q−F−alpha = −14,
Bt = C*(X+K0*q)−F*q = −14*(X+288)−32,
t = Bt/b,
sigma = ell+k+s−t−tau.
```

This is an explicit positive integer. The old first norm implies `b` divides
its old `Bt`; changing alpha by 31 changes `Bt` by `−31*(X+288)`, so `t` is
an integer. The new Bt is negative. Also `tau<ell+k` since
`(ell+k)²−tau²=ell*k+k²−1>0`, so `sigma>0`.

The rank `R` is unchanged: `G=b*(q−F)+alpha` increases by 31, while
`MC` decreases by `31*(q²−1)=31713`; here `J=1`. The graph's non-first
residuals depend on F, alpha and MC through this retained rank and are exactly
the three zero residuals in the source tuple. For the first residual, with
`M=q³*b`, the candidate expression is

```
Z = M*(ell+k−sigma)+Y*b−q³*Bt = M*tau,
```

so its square is `M²*(1+ell*(ell+k))`. Thus the first residual also vanishes.
All thirteen inputs are positive.

## The finite scalar-repair window fails

For a nonnegative shift `delta`, the cited criterion uses
`F'=F−delta`, `alpha'=alpha−b*delta`. Since this witness has `F=1`, positivity
of `F'` forces `delta=0`. But `Bt<0`, so `delta=0` cannot make `Bt'>0`.
Equivalently its upper bound `D=min(F−1, floor((alpha−1)/b))` is zero while
its least admissible shift `delta0` is positive. This is a counterexample to
universal success of **that restricted repair at arbitrary integer ports**;
it does not rule out other changes of witness or other ports.

Run the deterministic finite graph and scalar controls with:

```
python3 -I -S -B research/ordinary13-folded-root86-negated-full-zero-window/check.py > /tmp/folded-window.json
cmp /tmp/folded-window.json research/ordinary13-folded-root86-negated-full-zero-window/result.json
```

The checker pins the two graphs, checks relevant use sites and exact scalar
constants, and tests the described polynomial transport at 15 small integer
assignments. Those controls do not independently prove the unbounded
symbolic toy construction, substitute for its cited review, or check file or
PDF semantics.

## A separate positive-port witness

The same obstruction also has the following independently proposed symbolic
construction with **all four fixed ports positive**:

```
beta=31, K0=9, MC=30658, MF=1,
J=F=1, alpha=34, q=32, C=−3,
G=995, R=1048575=2^20−1, X=2^R, N=(R−1)/2.
```

Here `R=3 mod 4`, `X=1 mod 31`, and
`Bt=−3*(X+288)−32<0` is divisible by 31. Define `Y` by the finite binomial
sum in the cited toy-parent packet. As `N=2^19−1`, the reviewed
central-binomial valuation gives `v2(Y)=popcount(N)−1=18`, so `q³|Y`.
The reviewed general Pell/floor construction applies at this `R` and `X`:

```
s=Y/q³, E=X*Y, m=E*Y, a=E+Y, H=4*a+3,
Delta=(a+2)²−1, U=Y*q², w=X/q,
k=2*psi_(2m+1)(N+1), tau=chi_(2m+1)(N+1),
c=psi_(a+2)(R), D0=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta,
gamma0=(D0−X−a*c)/H,
gamma=gamma0−w+(k−R−1)/U.
```

`chi` and `psi` denote the Pell coefficients defined in the cited packet.
The inherited floor inequalities give positive `eta,zeta`; the first Pell
congruence gives `E|(k−R−1)`, hence `U|(k−R−1)` since `X/q²` is an
integer. The trace sum gives `gamma0>=2^(R−2)>w`, so `gamma` is positive.
The definitions give `Dstar=U*D0` and both main and first Pell norm identities.
Set `t=Bt/31` and `sigma=ell+k+s−t−tau` as above, where `ell=m*k`;
then `sigma>0` and `Z=M*tau`.

For the remaining inputs use the same strong and auxiliary construction as
the cited toy-parent packet: let

```
f+L*sqrt(Delta)=(D0+c*sqrt(Delta))^c,
i=Delta*L/c²,
S=Delta*L,
V=chi_S(R)/S, y=psi_S(R),
T=(V+c+f²*R)/(c*f²), u=y−V.
```

The cited Pell and Chebyshev arguments give positive integers `f,i,T,u`,
`g72=0`, and `Fa=1`. Consequently all four residuals vanish. Since `F=1`
and `Bt<0`, the same scalar window is empty. This second witness has
different toy ports from the compact44 instance and does not establish the
failure of repair at that instance. Its unbounded inheritance and complete
scope are submitted for independent review.

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-negated-full-zero-window-independent/`.
