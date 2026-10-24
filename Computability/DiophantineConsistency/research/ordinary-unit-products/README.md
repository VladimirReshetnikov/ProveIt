# Materialized ordinary-norm endpoint: twelve positive variables, 100/70

[p12_ordinary_degree70.json](p12_ordinary_degree70.json) is a literal
division-free polynomial circuit in **twelve strictly positive integer
unknowns**, with **100 live binary operations and exact degree 70**.
It materializes the twelve-variable equation in the arriving `report.zip`
manuscript, SHA256
`4130601f3f13426318c4266a87e2d6ce9cf7205c711a9c226782e87744be2754`.
That archive contains only `report.tex`: the literal graph is reconstructed
here, rather than attributed to an absent delivered JSON file. This is not
a novelty or priority claim.

The point improves the normalized-norm 101/78 checkpoint in both measures.
The arithmetic convention charges every binary `+`, `-`, `*`, including
squaring and scalar multiplication; reuse and integer leaves are free.
The circuit uses 55 multiplications, 26 additions and 19 subtractions.
All gates, all twelve inputs, and all four fixed ports are live.

The proof below is ordinary mathematics. It composes with the same named
ordinary native/compiler calibration as the earlier compact44 equations.
No Lean work was performed; formalization is paused. This is not a new
end-to-end Lean certificate or encoded internal-ZFC derivation.

## Complete equation and exact domain

Use the entire compact44 tuple `beta,K0,MC,MF`, with
`beta=2^590069-1`, `K0=K`, and the already shifted `MF_source` port.
The tuple is exactly the one pinned in the neighboring
[normalized-norm checkpoint](../short-unit-products/CHECKS.json).
Do not mix ports or shift MF again.

The only unknowns are

```text
j,F,alpha,t,T,X,Y,r,eta,zeta,n,gamma > 0.
```

Use every [shared carrier abbreviation](../short-unit-products/README.md#binding-and-shared-carrier)
with `m=6`. In particular

```text
J=6j+1, q=beta J+1, C=q-F-alpha,
E=XY, k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
Delta=a²+H=(a+2)²-1, ell=EkY,
M=q³(q-1), W=(q-1)k+1, Bt=(qK0+X)C-qF,
Z=M(ell+k+r)+(q-1)Y-q³W Bt,
A0=Z²-M²[ell(ell+k)+1],
R=[(q-1)(q-F)+alpha](q²-1)+(MC+q MF)J,
v=k-R-1, U=q²Y,
Dstar=U(X+ac)+H(U gamma+qE-v),
A1=Dstar²-U²(1+Delta c²).
```

The changed merger uses the ordinary strong norm:

```text
f=t+1, rho=f²-1, Q=Delta rho, d=c⁴,
V=f²(cT-R)-c,
h(z)=(1-Q)z²+2(1-Q)Vz+V²-1,
bn=2(1-Q)(n+V), AN=d h(n)+(1-Q)Q,
N=AN²-d bn²Q.

P12=(1+A0)(1+A1)(1+N)-1=0.
```

All names are polynomial abbreviations, not quantified coordinates.
The evaluator computes `h(n)=(V+n)²-Q[(V+n)²-V²]-1`.
Relative to the normalized-norm checkpoint, this replaces
`d=Delta c⁴, AN=d h(n)+(1-Q)rho, N=AN²-d bn²rho`
by the displayed ordinary versions. It removes one multiplication and
lowers the degree of N from 50 to 42.

## Early recovery: no strong or auxiliary equation is assumed

As beta and `J` are odd, `q` is even. Both M and U are even, and bn is
even. The three residuals are squares modulo four. At `P12=0`, every
integer factor is a unit; `-1` would require a residual equal to `-2`,
which cannot be a square modulo four. Thus `A0=A1=N=0`.

The first two equations alone give the following facts.

1. From `A0=0`, `Z/M` is a rational square root of an integer, hence
   integral. Reducing `M|Z` modulo `q³` and `q-1` gives `q³|Y` and
   `q-1|Bt`. If `s=Y/q³>0`, `b=Bt/(q-1)` and `tau=Z/M`, then
   `tau=ell+k+r+s-Wb` and `|tau|<ell+k`. Thus `b>0`, `Bt>0`, and
   consequently `C>0`.
2. The actual masks satisfy `0<MC<beta`, `0<MF<2beta` and `K0>=1`.
   They imply `0<(MC+q MF)J<(q-1)(1+2q)`. With `C>0`, the usual
   expression `G=q alpha+(q-1)C` gives `q<=G<=q²-q`; hence
   `q>=16` and `3q<R<q⁴-2`. Also beta is one modulo three,
   `J=1 (mod 3)`, and `q=2 (mod 3)`. Since `q³|Y`,
   `H=3 (mod q)` and `gcd(q,H)=1`.
3. `U=q²Y>=q⁵`. Since `v<k` and `c>kY`,
   `Dstar>Uac-Hk>k(UaY-H)>0`. Rational-square-root integrality in
   `A1=0` yields a positive integer `D=Dstar/U` satisfying
   `D²-Delta c²=1`, and `U|H(qE-v)`.
4. The **divisibility**, rather than just the inequality, `q⁵|U`
   follows from `q³|Y`. Since `gcd(q,H)=1` and `q⁴|qE`, the last
   carrier condition gives **`q⁴|v` before any strong-rank recovery**.

Put `A=a+2` and `P0=2XY²+1`. First/main Pell classification gives
positive indices `m1,p` with

```text
|tau|=chi_P0(m1), k=2 psi_P0(m1), c=psi_A(p).
```

Here `Y>=q³` implies `P0>A`, while `c>k`, so monotonicity of the Pell
sequences gives `p>m1`. The first recurrence gives
`k=2m1 (mod 4XY²)`. As `q⁴|4XY²`, it follows that

```text
2m1=R+1 (mod q⁴).
```

Both `2m1` and `R+1` are positive and `R+1<q⁴`; the integer multiplier
of q⁴ is therefore nonnegative. Consequently
`m1>=(R+1)/2>=24`, and `p>m1`. This estimate has used only the two
carrier equations, not N, the strong norm, an auxiliary index, or `q|X`.

In particular `p>=6`. The explicit identity

```text
psi_A(6)-A(A²-1)²=A(31A⁴-30A²+5)>0   (A>=2)
```

proves **`c>A Delta²`**. Pell growth also gives `c>2p`.
Since `m1>=2`, `k>=4P0` and
`c>kY>8XY³>=8q⁹>2R`. Thus `f>=2,T>=1` imply
`V=f²(cT-R)-c>c>1`. All size hypotheses for ordinary strong-rank
recovery are now established without a circular dependency.

## Elimination and ordinary strong-rank recovery

Now `Q>1`, `d>0` and `bn!=0`. At `N=0`, define rational proof coordinates

```text
i0=AN/(d bn), u0=n-i0, y0=V+u0.
```

Then `d i0²=Q` and `h(u0)=0`, so
`QV²-(Q-1)y0²=1`. The adjacent-coefficient descent proved in the
[normalized-norm note](../short-unit-products/README.md#rational-integrality-lemma)
shows `y0` is integral. Thus `u0` and `i0` are integers. Put
`i=|i0|>0` and `y=|y0|`. We recover

```text
(ic²)²=Delta(f²-1),
(ic²)²V²-[(ic²)²-1]y²=1.
```

These are **ordinary** strong/auxiliary equations. Dividing i by Delta
is not justified and is not part of the reconstruction.

The required ordinary rank theorem and source kernel are retained in
[ORDINARY_BLANK_PROOF.md](../../con-zfc-diophantine-forms/35-cancel12/sources/catalogue/25-hybrid12/upstream/ORDINARY_BLANK_PROOF.md),
Sections 4–7 (source SHA256 is in [CHECKS.json](CHECKS.json)). Their
hypotheses are precisely `A>=2`, `c=psi_A(p)>A Delta²`, and the
displayed positive ordinary strong equation. The theorem gives

```text
f=chi_A(m), p|m, c|m, m>=c>2p,
ic²=Delta psi_A(m), c²|f²-1.
```

For clarity, its rank-size step is as follows. Write
`A=chi_F0(e)`, `Delta=(F0²-1)S²`, `S=psi_F0(e)<A`. Classification
of the ordinary norm gives `f=chi_F0(u)` and
`ic²=(F0²-1)S psi_F0(u)`. Strong divisibility, with
`g=gcd(u,ep)` and `b=psi_F0(g)`, gives `b>=c/Delta`.
If `g<ep`, then `2g<=ep` and
`2b²<psi_F0(2g)<=Sc<Ac`, contradicting `c>A Delta²`.
Hence `ep|u`. Write `u=em`, `m=pt`; the recurrence modulo c² gives
`c|Delta t`. Since `gcd(c,Delta)=gcd(p,Delta)` divides p, one gets
`c|m`. The remaining displayed conclusions follow as in that source.

The signed auxiliary-index theorem now applies: `V=-c (mod f)` and,
using `c²|f²-1`, `V=-R (mod c)`. Together with `c>2p,2R` it gives
**`p=R`**. Returning to the early congruence, `0<m1<p=R<q⁴`
forces `2m1=R+1` exactly. Thus `v=k-2m1` is a positive multiple
of `4XY²`. In particular `U|v`, since `4XY²/U=4XY/q²` is integral
already from `q³|Y`. The main divisibility gives `q|HX`, hence `q|X`.

Set `w=X/q>0`, `h=v/E>0`, and
`gamma_old=gamma+w-v/U`. They are integers. Since
`D>(a+1)c` and `c>X`, the last coordinate is positive and
`D=X+ac+H gamma_old`. Also
`Bt=q[(K0+w)C-F]` is positive and divisible by q-1, giving the
positive **shifted** transport coordinate
`z=[(K0+w)C-F]/(q-1)`. The old convention is `z_old=z+1`.
Finally choose `T_old=fT`, preserving
`V=c(T_old f-1)-Rf²`.

These are the six equations (S) in the retained **ordinary source
kernel**. One can also restore the two extra coordinates in compact44's
literal sixteen-positive-variable kernel directly:

```text
o=f(cT-R)>0,       j_source=(V+R)/c>0.
```

The second coordinate is integral since `c²|f²-1`, and its positivity
follows from `V,R>0`. They satisfy `of-c=V=j_source c-R`.
Thus the recovered tuple satisfies precisely the seven equations in
[compact44's proof, Section 7](../../con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md),
using the same whole tuple and the shifted transport coordinate z above.
The cited ordinary compiler theorem therefore supplies a finite syntactic
ZFC refutation. This last
compiler/calibration step is inherited; neither hashes nor finite tests
discharge it.

## Completeness

A finite refutation supplies canonical normalized compact44 witnesses.
They have `J=1 (mod 6)`, `J>1`; choose `j=(J-1)/6>0`.
Keep their f and auxiliary pair, and replace the normalized multiplier by
`i_ordinary=Delta i_normalized`. Then
`(i_ordinary c²)²=Delta(f²-1)=Q`, and the auxiliary coefficient and
V are unchanged. Set `t=f-1>0` and `n=i_ordinary+u>0`.

The adaptive lift is the one from source73:
`gamma=gamma_old-w+v/U`. It is a positive integer because v is a
positive multiple of `4XY²` and
`v/U>=4XY/q²>w`. Both carrier residuals vanish. The exact identity

```text
N |_(Q=d i²) = d² h(n-i)h(n+i)
```

then gives N=0, since `n-i=u` and the auxiliary equation says `h(u)=0`.
Thus P12=0. This proves both existence implications after composing with
the named ordinary source/calibration theorem. Negating yields its ordinary
equivalence with syntactic Con(ZFC); an encoded ZFC derivation and complete
Lean certification remain open.

## Exact degree and reproduction

With every unknown of degree one and fixed ports of degree zero, the
carrier leaders are exactly L0,L1 in the normalized note, of degrees
15 and 13. Write `q0=6 beta j`, `k0=eta+zeta`,
`R0=q0³(q0-F)`. Here `deg(d)=8`, `deg(Q)=6`, `deg(h(n))<=13`,
`deg(bn)<=12`, so `deg(AN)<=21`, and the subtracted tail of N
has degree at most 38. Its degree-42 leader is

```text
LN=4k0⁸X⁴Y¹²t⁸R0²n².
```

The degree-70 product `L0 L1 LN` has monomial
`j¹⁸ F² eta¹¹ X⁸ Y¹⁹ t⁸ n² gamma alpha` with coefficient
`64(6 beta)^18>0`, independent of K0,MC,MF. Thus the degree is exact
after specializing the actual coefficient tuple.

Run `python3 build.py`, `python3 check.py`, and `python3 -O check.py`
with SymPy 1.14 available. The builder reuses only our pinned carrier
builder; the independent checker imports no builder. It checks the entire
carrier-prefix identity, topology/liveness/counts, exact ordinary merger
and factorization, the early rank-growth polynomial, all relevant
negative-unit residues, the displayed coefficient, complete-circuit
univariate degree, and 160 independent scalar formula comparisons.
The ordinary universal proof is the argument above, rather than those
finite diagnostics. The candidate's circuit hash and normal/optimized
receipts are [CHECKS.json](CHECKS.json) and
[CHECKS_OPTIMIZED.json](CHECKS_OPTIMIZED.json).
