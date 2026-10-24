# Independent mathematical review of the twelve-integer construction

Reviewed source: `agent_alternative/INTERPOLATION12.md`, the complete
twelve-coordinate construction communicated during this research session.
The review covers the new algebra, nonvanishing/realness bootstrap,
radical extraction, homogeneous divisibility, full residue interpolation,
completeness witness order, and exact degree argument. It includes the
final product weights and the homogeneous first-root bound, giving degree
4832. The inherited signed native argument is reviewed separately by the
frontier-audit agent. Its direct normalized strong-rank proof needs no
extension of the ordinary strong saturation lemma to an even multiplier.

## Conclusion

**PASS for the new mathematical reduction**, composed with the explicitly
cited inherited ordinary signed native calibration. This report does not
independently repeat the entire inherited machine/compiler proof.
I found no hidden Diophantine coordinate or circular witness choice in
the new twelve-variable formula. The listed variables are exactly

`j,C,z,h,r,v,w,T,c,n,t,s`.

The eight-word count in the original sentence introducing the outer
coordinates is a harmless wording error: the list `j,C,z,h,v,w,c`
contains seven coordinates. Those seven, followed by `t,s,r,T,n`, give
the asserted twelve.

## 1. Intersective polynomial and nonvanishing

The quintic

`pi(x)=(x^2+31)(x^3+x+1)`

has a root modulo every positive integer. For an odd prime other than
31, an irreducible cubic factor has Frobenius a three-cycle, so its
discriminant -31 is a quadratic residue; if the cubic is reducible it
has a linear root. These roots are simple since the cubic discriminant
is nonzero at those primes and the quadratic has nonzero discriminant.
At p=31 the cubic root 3 is simple (derivative 28), and at p=2 the
quadratic has roots to all powers because -31 is 1 modulo 8. Prime-power
lifting and finite CRT therefore supply the stated result.

The cubic is irreducible over Q by its rational-root test, and the
quadratic has no real root. Thus pi has no root in a real field of
degree at most two. Also

`pi'(x)=5x^4+96x^2+2x+31>0`

for every real x. For every nonzero real H the derivative of
`Phi_H(x)=H^5*pi(x/H)` is `H^4*pi'(x/H)>0`. Consequently, for the
actual unconditional `Dm>0`, the quadratic-algebra coefficient

`B=[Phi_H(u+sqrt(Dm))-Phi_H(u-sqrt(Dm))]/[2sqrt(Dm)]`

is strictly positive. Both factors `A±B sqrt(Dm)` are nonzero.

I specifically checked the possible circularity at S=0. It does not
occur: the front end has `Y=(2v+1)q^3` nonzero for every integer v,
`|X|>=64`, `|Y|>=4096`, and hence `Delta>1`, `Dm>=1` before any equation
or guard. Therefore the argument excludes S=0 on the full integer domain,
including all initially inadmissible native assignments.

## 2. Realness and separation

At I=0, Da=1. At I nonzero, the actual identity `I=s*r*c^2` gives
`c!=0` and `|I|>=c^2`; therefore `Df>|c|+1`. With the integer
`b=c-R+4IT`, this makes `|V|>=1` and proves `Cy>0`, `Da>0` whenever
Q>1. Thus Dm,Df,Dt,Da are positive before the guard is used.

The norm at S=0 is exactly `(A^2-B^2 Dm)^16`, which is nonzero. Hence
S,I,s,r,c are nonzero at every zero. A negative Dg would then contribute
the only nonzero imaginary term in a vanishing norm factor, which is
impossible. The subsequent deduction `P>0` and then `G>0,eta*zeta>0`
is valid in that order.

The final product weights are odd on the full integer domain. Their
nonvanishing therefore precedes the strict guards, as required by this
imaginary-root argument. Section 6 below gives the individual bounds and
proves separation after the guards, without invoking any square extraction
or Pell rank theorem in establishing those bounds. The square-class
argument then extracts all five rational roots, and integer radicands make
them integral. The auxiliary adjacent-coefficient descent makes
`y=ytilde/delta` integral as asserted.

## 3. Homogeneous divisibility

The relation from one norm factor gives

`I H^5 | Phi_H(d-b0+HT)`.

For a prime p with `p^e || H`, suppose `p^b || (d-b0+HT)` with b<e.
The first monic term of Phi has valuation 5b. Each other term has
strictly greater valuation:

```
32H^2 x^3: at least 2e+3b,
H^3 x^2:   3e+2b,
31H^4 x:   at least 4e+b,
31H^5:     at least 5e.
```

The unique least term cannot cancel, contradicting divisibility by
`p^(5e)`. Thus H divides d-b0. This uses no coprimality between I and H,
and applies equally to negative H. The recovered gamma is an integer.

The two restored auxiliary coordinates are also literal integer
polynomials on every zero:

```
o=f(c-R+4IT),
j_aux=Delta*s^2*r^2*c^3*(c-R)+4*s*r*c*Df*T.
```

Direct expansion verifies `V=f*o-c=c*j_aux-R`.

## 4. Full residue interpolation

The corrected period `lambda=4*n0*f` is essential and sufficient.
Writing `alpha=A0+sqrt(Delta)` and `beta=alpha^n0=f+I sqrt(Delta)`,
the norm-one identity gives `beta^2=2f beta-1`. It follows that

`alpha^(4n0)=1-4f alpha^n0 (mod f^2)`.

Raising to the integer power f gives the identity modulo f^2. This
checks the two-coordinate Pell period, rather than just the first one.

For every prime p dividing I, the bound `v_p(I)>=v_p(n0)` is valid.
For odd p dividing Delta the rank of appearance is p; otherwise it
divides p-1 or p+1 and is prime to p. The usual binomial lifting of
the norm-one unit then gives the valuation bound. At p=2, even A0
and the doubling identity give

`v_2(psi_A0(n0))=v_2(n0)+v_2(A0)`

for even n0. Since I is a multiple of 4 and f is odd with gcd(f,I)=1,
these bounds imply

`gcd(lambda,4I^2) | 4I`.

Consequently the prescribed congruences

`L0=R (mod lambda), L0=R-4Ia (mod 4I^2)`

are compatible for every class a modulo I. Their solutions are 3 modulo
4 and can be chosen positive. The exact Chebyshev recurrence proves

`chi_(Delta I)(L0)/(Delta I)=-L0 (mod 4(Delta I)^2)`.

The factor 4 is valid, not an assumed strengthening of a congruence
modulo `(Delta I)^2`. The other Chebyshev identity, together with the
period modulo f^2, gives `V0=-c (mod f^2)`.

For

`N0=V0+c-f^2(c-R)`,

we therefore have `f^2 | N0` and `N0=4Ia (mod 4I^2)`. The premise
`c=R (mod4)` supplies `f^2(c-R)=c-R (mod4I^2)`.
It follows that `T=N0/(4I f^2)` is integral. Finally

`f^2 T=N0/(4I)=a (mod I)`

and `f^2=1 (mod I)` prove `T=a (mod I)` exactly. The intermediate
use of `f^2=1 (mod I)` should be stated explicitly when presenting this
last deduction.

The strong I,f pair is fixed before a is selected. The lemma therefore
supports the later choice of a root of `pi(T+gamma)` modulo this same I.
There is no dependency cycle between the strong witness and the
intersective congruence.

## 5. Completeness witness order

The complete order is valid:

1. canonical native outer coordinates;
2. the joint-positivity witness t;
3. a Pell witness s,g for the positive P (or s=1,g=0 if P=1);
4. strong I,f with `4s c^2 | I`, then `r=I/(s c^2)`;
5. an intersective class a, followed by interpolated T,y;
6. the four product weights and the final integral n.

For P>=2, the coefficient `3P-4` is positive and 2 modulo 3, hence
nonsquare; the required Pell equation has a positive solution. For P=1
the stated exceptional choice satisfies Dg=0 exactly. The canonical
congruence c=R modulo 4 follows in fact for any even A0 with R=3 modulo
4, from the recurrence `psi_A0(m+2)=-psi_A0(m) (mod4)`.

No quantity defining the weights uses n. The last assignment therefore gives
the required norm factor without retroactively modifying an earlier
choice.

## 6. Final product weights and the homogeneous first-root bound

This section audits the final degree-4832 polynomial. The initial common
weight of degree 114 and its degree-16000 norm are retained only as the
separate compact-circuit companion. The intermediate degree-8832 and
degree-5984 bounds are superseded for the main equation.

Write `ell=XY^2`. To avoid ambiguity, `b=X+ac` is the original main
congruence offset, while `M0` below is a radical bound. Define

```
Bb = 1+c^2+R+c^2(s^2+r^2)(T^2+1),
K = T^2+c^2+1,
M0 = 256K^2,
Ma = Q(Df Bb+c^2+1),
Mf = Delta+I^2+3,
Mt = 2+ell^2+k^2,
wa = 2M0+1,
wf = wa(2Ma+1),
wt = wf(2Mf+1),
wg = wt(2Mt+1).
```

The final five radicands, in order, are

```
A0 = B^2 Dm,
A1 = S^2 wa^2 Da,
A2 = S^2 wf^2 Df,
A3 = S^2 wt^2 Dt,
A4 = S^2 wg^2 Dg.
```

The center is still `Sn-A`. Each weight is odd on every integer
assignment, hence nonzero even before any positivity guard. This matters:
nonzero weights are needed to recover `Dg>=0` before proving `R>0` and
using the signs of the bound polynomials.

### 6.1. The guard implies R>0 before square extraction

Set `Uc=cone_A F` and `Zc=cone_B C`. From `G>0` one obtains
`Uc Zc>0` and

`|q-(Uc+Zc)|<sqrt(Uc Zc)<=(|Uc|+|Zc|)/2`.

The authentic constants `cone_A,cone_B>=2` imply that q,F,C have a
common nonzero sign, `|q|>|F|+|C|`, and `alpha=q-F-C` has that same
sign. If q>0, both terms in

`R=(q alpha+(q-1)C)(q^2-1)+(MC+q MF)J`

are positive. If `q=-Q0<0`, write `C=-C0`, `alpha=-alpha0` with
`C0,alpha0>0`. The first factor is then
`Q0 alpha0+(Q0+1)C0>0`. Also `J=-(Q0+1)/beta<0`, and
`MC-Q0 MF<0` by the authentic coefficient bound `0<MC<beta<MF`.
The mask term is therefore positive as well. Thus R>0 in both cases.
This argument uses neither square extraction nor any Pell rank result.

### 6.2. The auxiliary, strong, and first-root bounds

The inequalities

`4|srT| <= (s^2+r^2)(T^2+1)` and `|c|<=c^2+1`

give `|c-R+4IT|<=Bb` once R>0. Hence
`|V|<=Df Bb+c^2+1`. With `Q>1` and `Da>0`,

`sqrt(Da)<Q|V|<=Ma`.

The other two estimates are

```
sqrt(Df) <= 1+sqrt(Delta)|I|
         <= 1+(Delta+I^2)/2 < Mf,
sqrt(Dt) <= 1+(|ell|+1)|k|
         <= 2+ell^2+k^2 = Mt.
```

The first-root estimate uses `ell(ell+1)>=0` for every integer ell,
then `sqrt(ell(ell+1))<=|ell|+1` and `2|xy|<=x^2+y^2`.

### 6.3. The sharper main radical bound

After S is known nonzero, `c!=0`, `|I|>=c^2`, and `|c|>=1`.
Uniformly in every front assignment, `|X|>=64`, `|Y|>=4096`, and
`|a|=|X+1||Y|`. Thus `|a|>3`, `|X|<|H|`,
`|a/H|<1/3`, and `2|a+2|<|H|`.

Introduce real quantities for this proof only,

`y=u/H=T-b/H`, `z=sqrt(Dm)/|H|`.

They are not additional Diophantine coordinates. Since `b=X+ac`,

```
|b/H| < 1+|c|/3,
y^2 < 3(T^2+1+c^2/9) <= 3K.
```

Also `Dm=1+((a+2)^2-1)c^2<=(a+2)^2 c^2`, whence
`z<|c|/2` and `z^2<=K`. The exact coefficient identity is

`B/H^4=5y^4+10y^2 z^2+z^4+96y^2+32z^2+2y+31`.

Using `2|y|<=y^2+1`, this gives

`B/H^4 <= 76K^2+323K+32 <= 431K^2`.

Consequently

```
B sqrt(Dm)/|S| = (B/H^4) z/|I|
              < 431K^2 |c|/(2|I|)
              <= (431/2)K^2 < 256K^2=M0.
```

This estimate needs S nonzero but does not need the guard or any Pell
classification. The sign of H causes no change because H occurs to an
even power in the normalized coefficient and as |H| in z.

### 6.4. Product-weight separation and completeness

After the guards, the four bounds are positive. Put

```
x0=B sqrt(Dm)/|S|,
xa=wa sqrt(Da), xf=wf sqrt(Df),
xt=wt sqrt(Dt), xg=wg sqrt(Dg).
```

The checked bounds imply

```
x0 < wa/2,
x0+xa < wa(1/2+Ma)=wf/2,
x0+xa+xf < wf(1/2+Mf)=wt/2,
x0+xa+xf+xt < wt(1/2+Mt)=wg/2.
```

Every nonzero integer radicand has square root at least one. Therefore
each next nonzero radical term has magnitude strictly greater than twice
the sum of all preceding terms. If Dg is zero, its term is simply absent.
Grouping terms by rational square class proves that a nontrivial square
class cannot contribute zero: its largest term dominates every earlier
term in that class. Thus the same root extraction applies to these final
weights.

In completeness, after the existing witnesses have been selected, set

`n=(A+B d)/S+wa ytilde+wf f+wt tau+wg g`.

The first quotient is integral by the intersective congruence, all roots
are integral, and the weights are already fixed. No new witness or
dependency cycle is introduced.

## 7. Independent exact degree calculation for the final equation

I recomputed the source degrees, rather than accepting a metadata field:

```
a 6, Delta 12, R 5, k 7, eta 11, P 44,
I 4, Df 20, Q 32, V 25, Cy 82, Da 114,
Dt 34, Dm 14, Dg 46,
u 7, A 35, B 28, S 34, Z 35,
Bb 6, M0 4, Ma 58, Mf 12, Mt 20,
wa 4, wf 62, wt 74, wg 94.
```

The five radicands have degrees `70,190,212,250,302`. The last is
uniquely largest and its square-root degree 151 exceeds the center's
degree 35. Taking that radical in all 32 factors gives `A4^16` with
coefficient 1; every other norm contribution has lower total degree.
The exact degree is therefore `16*302=4832` once the last leading form
is shown nonzero.

Write

```
q0=6 beta j,
Y0=2q0^3 v=2^4 3^3 beta^3 j^3 v,
a0=2^7 3^5 beta^4 j^4 w v,
I0=s r c^2.
```

The leading forms needed for the last radicand are

```
lead(M0)=2^8(T^2+c^2)^2,
lead(Ma)=a0^6 I0^4 c^2(s^2+r^2)T^2,
lead(Mf)=a0^2,
lead(Mt)=a0^2 Y0^2,
lead(S)=2^10 I0 a0^5,
lead(Dg)=-3s^2 Y0^4 h^4 a0^4.
```

Hence

```
lead(A4)=-3*2^44 (T^2+c^2)^4 a0^34 I0^10 c^4
                    (s^2+r^2)^2 T^4 s^2 Y0^8 h^4,
lead(P12)=2^704*3^16 (T^2+c^2)^64 a0^544 I0^160 c^64
                    (s^2+r^2)^32 T^64 s^32 Y0^128 h^64.
```

In particular the coefficient at

`j^2560 w^544 v^672 h^64 s^192 r^224 c^384 T^192`

is exactly `2^5024*3^3120*beta^2560>0`. The exponents sum to 4832.
The maximal T exponent uniquely selects T from every `(T^2+c^2)`
factor, while the stated r exponent uniquely selects r from every
`(s^2+r^2)` factor. There is no cancellation. The equally valid
endpoint `s^256 r^160` in place of `s^192 r^224` has the same
coefficient and appears in the builder metadata.

This is an independent mathematical degree check. Literal circuit counts,
source-byte hashes and finite modular transcription checks are separate
artifacts and were not needed for this logical review. Such finite checks
are not a proof-assistant verification of the complete unbounded theorem.
