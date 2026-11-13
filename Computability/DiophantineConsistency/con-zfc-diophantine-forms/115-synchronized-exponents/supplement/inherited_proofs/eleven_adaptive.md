# Eleven positive variables, 111 operations and exact degree 211

This refines the polynomial-shears archive (SHA256 `978f7e8be846732c1330f3a75a0fe38871432f79951b8eaad6ef096f3e03e165`) by replacing its main carrier `S=4qY,U=qS` with `S=qY,U=qS`. The separate arriving Pell-congruences proof justifies this adaptive modulus. The only deleted circuit gate multiplies qY by four. The source archive, stored parent literal, and proof snapshot remain unchanged.

The complete equation is [positive11.json](positive11.json). Its only unknowns are

```
j,F,alpha,i,T,X,Y,n,eta,zeta,gamma > 0.
```

The four fixed ports are the whole compact44 tuple, `beta=2^590069-1`, `K0=K`, `MC`, `MF=MF_source`, where MF is already shifted. Actual payloads are linked by the literal's binding and authenticated by [BUILD.json](BUILD.json). Fixed ports and all ordered register names below are polynomial abbreviations, not additional unknowns.

## Formula

```
J=3j+1, q=beta J+1, C=q-F-alpha,
E=XY, k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
Delta=a²+H=(a+2)²-1, ell=EkY, I=i c²,
R=[(q-1)(q-F)+alpha](q²-1)+(MC+q MF)J,
Bt=(qK0+X)C-qF, M=q³(q-1), Dtau=ell(ell+k)+1,
Df=1+Delta I², Q=Delta²I², delta=Q-1,
Tbar=T+F+alpha, Cf=(a+2)I,
V=Df(c Tbar-R)-c, L=k Tbar, W=1+(q-1)L,
Zbar=M(ell+k+n+L+V+Cf)+(q-1)Y-q³W Bt,
v=k-R-1, S=qY, U=qS,
shift=U gamma+SX-v, Dstar=U(X+ac)+H shift,
A1=Dstar²-U²(1+Delta c²).

A=M² Dtau, Bf=M² Df, Cnum=M²(QV²-1),
Tn=delta² A Bf, Rn=delta Cnum,
Jn=delta(Zbar²-A-Bf)-Cnum,
Ncenter=Jn²-4[Tn+Rn(A+Bf)],
N8=Ncenter²-64 Tn Rn Zbar²,
P=N8+A1+N8 A1=0.
```

This is an ordinary integer polynomial. The formula and literal have no roots, rational divisions or variable exponents.

## The unchanged local reduction

The retained [parent proof](upstream/PROOF112.md), Sections 2–6, proves the following ordinary facts. The steps preceding the main adaptive recovery do not use the scalar four in S or U.

1. `N8=0` is the eight-conjugate norm for the signed roots of `Dtau`, `Df`, and `Dy=(QV²-1)/(Q-1)`, after multiplying by the strictly positive `delta⁴ M⁸`. The positive radicands are distinct and no signed three-root sum vanishes: if `c Tbar-R=0`, the strong root dominates; otherwise the auxiliary root dominates. A nonzero rational sum of three such roots forces each root rational. Integral squares and the adjacent-coefficient Pell descent give integral roots `tau*,f*,y*`.
2. `M|Zbar` restores `q³|Y` and `q-1|Bt`, without a sign assumption on C. `A1=0` gives an integral main root whose absolute value and positive ordinate c classify as `chi_(a+2)(p),psi_(a+2)(p)`. The sign is initially unnecessary. First Pell classification gives `k=2psi_(2XY²+1)(m)` and `|tau*|=chi_(2XY²+1)(m)`. The case m=1 contradicts c's first possible main Pell value, so m>=2. Consequently `c>8XY³>=8q⁹`, before C is positive.
3. The unconditional mask estimate `|R|<q³(q+F+alpha)` and the offset `Tbar=T+F+alpha` imply `V>1` at this stage. The strong-root center satisfies `f<Cf`. The auxiliary positive gap satisfies `0<y-V<L=k Tbar`. Hence `L+V+Cf-f-y>0`. The root equality rules out `Bt<=0`, giving `Bt>0,C>0` and the authentic mask bounds `3q<R<q⁴-2`. It also makes `r=n+L+V+Cf-f*-y*>0` and restores the first carrier with weight L.
4. With `C>0`, `Dstar>Uac-Hk>0` for our positive `U=q²Y>=q⁵`. Thus its extracted main root is positive. Classification gives `m<p`, `c>2p` and `c>2R`. The normalized strong equation `f²-Delta I²=1`, with `I=i c²`, yields a strong index divisible by pc and larger than 2p. The signed auxiliary-index theorem uses `V=-c mod f` and `V=-R mod c` to give `p=R`. It uses neither the deleted quotient `q|X` nor an unproved exact first index.

The cited Pell classification, signed index and native canonical witness results are inherited ordinary mathematical theorems, as in the retained proof. Their full native/compiler calibration is not being inferred from finite tests.

## Exact adaptive recovery with S=qY, U=q²Y

This is the changed step, given in full. The integral main root gives

```
U | H(SX-v).
```

Since beta is 1 modulo three and `J=3j+1`, q is 2 modulo three. From `q³|Y` one has `H=3 mod q`, hence `gcd(q,H)=1`. Therefore

```
g=gcd(H,U)=gcd(H,Y)=gcd(3,Y) in {1,3}.
```

The exact cofactor matters: `gcd(q,g)=1` and `q³|Y` imply `q³|(Y/g)`. Put `mu=qY/g`; then `mu>=q⁴>R`. Cancelling only g from the main divisibility gives `U/g | SX-v`. As mu divides SX, it divides v. It also divides `4XY²`, since `q|Y`. First-Pell recurrence gives `k=2m mod 4XY²`, so

```
mu | 2m-R-1.
```

We already have `1<=m<p=R<mu`. Thus `|2m-R-1|<mu`, forcing `2m=R+1` exactly. Now v is a strictly positive multiple of `4XY²`. It is a multiple of U as well, since `4XY²/U=4XY/q²` is integral from `q³|Y`. Returning to the main divisibility gives `U|HSX`, hence `q|HX`, and finally `q|X` because `gcd(q,H)=1`.

All old source quotients are now integral:

```
w=X/q>0, h_index=v/(XY)>0,
gamma_old=gamma+w-v/U.
```

The main equation reads `d=X+ac+H gamma_old` for the positive main root d. Since `d>(a+1)c` and `c>X`, `H gamma_old>c-X>0`; thus gamma_old is positive. The positive first-carrier quotient gives

```
z_new=((K0+w)C-F)/(q-1)>0,
z_old=z_new+1.
```

It satisfies the authentic old transport equation `(K0+w)C+(q-F)-z_old(q-1)=1`. The authentic auxiliary parameter is `T_auth=f*Tbar`, so `c(T_auth*f-1)-R f²=V`. Absolute root signs restore positive strong/auxiliary coordinates. This is the same normalized native source, with no added calibration hypothesis.

## One equation and positive completeness

The finalizer is exact even when A1 is not a square modulo four. Indeed N8 is a square modulo four for every integer input. If `(1+N8)(1+A1)=1`, the integer factors are both +1 or both -1. The latter would force `N8=-2`, impossible modulo four. Hence `P=0 iff N8=A1=0`. There is no need to keep the scalar four merely to constrain A1's parity.

For the converse use canonical compact44 source witnesses. The retained parent proof supplies `J=1 mod 3,J>1`, `Y=q³s`, `X=qw`, `R=3 mod 4`, `m=(R+1)/2`, and normalized strong/auxiliary witnesses with `Tbar>F+alpha` and `Tbar>Cf`. These last strict bounds follow there from auxiliary Pell growth, before choosing the transport weight. Set `T=Tbar-F-alpha>0` and `j=(J-1)/3>0`.

The exact first index gives positive `v` divisible by `4XY²`. Thus

```
gamma=gamma_old-w+v/U
```

is an integer. It is positive: `v/U>=4XY/q²=4wY/q>w`, because `Y>=q³` and `q>=16`. This is the only altered inverse coordinate; it yields `Dstar=U*d` and A1=0.

Set `L=k Tbar>Cf,k`, and use the canonical quotient `b=Bt/(q-1)>=q`, first positive root `tau>ell`, and `s=Y/q³<k`. Choose

```
r=Wb+tau-ell-k-s > qW-2k > 2L,
n=r-L-V-Cf+f+y.
```

The auxiliary gap `y-V>0` and `Cf<L` give `n>r-2L>0`. All eleven supplied coordinates are positive. The identity `Zbar=M(tau+f+y)` makes N8=0. Thus every canonical refutation witness has a new positive zero.

This proves both existence directions with the same normalized native source as the parent. Composing with its named ordinary syntactic-refutation calibration, then negating, gives the ordinary ZFC-formalizable no-positive-zero equivalence with Con(ZFC). No new end-to-end Lean or internal object-ZFC derivation is claimed; formalization remains paused.

## Literal counts and exact degree

[build.py](build.py) authenticates the parent, renames its qY producer to S, deletes precisely the scalar-four gate, and leaves every other row unchanged. All 111 rows, eleven inputs and four ports are live: 63 multiplications, 31 additions, 17 subtractions. The two-residual system has 108 operations.

The norm is unchanged, with its exact 229-term double-center certificate and degree 198. The reduced main residual has degree 13 and leader

```
8q0² k0 X²Y⁴(q0²Y gamma+R0),
q0=3beta*j, k0=eta+zeta, R0=q0³(q0-F).
```

Consequently P has exact degree 211. The coefficient at

```
j^48 i^18 eta^39 X^30 Y^67 T² F⁴ alpha² gamma
```

is `2^9(3beta)^48>0`, independent of K0,MC,MF. This is the parent coefficient divided by sixteen, because both U factors in the gamma-containing main term lose their scalar four. [check.py](check.py) checks the exact norm/extraction/main identities, all sixty named cuts, topology/liveness, double-center expansion, leading forms and selected coefficient. It is an explicitly adapted version of the retained parent auditor, not a newly independent authorship claim. Normal and optimized receipts both pass.
