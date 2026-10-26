# Eliminating the index quotient by an auxiliary Pell residue

Research note, 25 October 2026. This note transforms the frozen equations
of ProveIt package `142-coprime-products-positive-centers`, without changing
its indexed943/radix67 coefficient tuple. The tuple is **not** interchangeable
with the later complemented47 or seven-marker tuples. All quantified
coordinates below range over the strictly positive integers.

| Complete literal source | Coordinates | Binary operations | Exact total degree |
|---|---:|---:|---:|
| `fixed_13_residue_70_degree206.json` | 13 | 70 | 206 |
| `fixed_13_residue_71_degree162.json` | 13 | 71 | 162 |
| `fixed_13_residue_q4_72_degree154.json` | 13 | 72 | 154 |
| `fixed_12_rational_74_degree438.json` | 12 | 74 | 438 |

One binary addition, subtraction, or multiplication costs one operation,
including squaring and multiplication by a numerical constant. Reuse and
integer leaves cost zero. All definitions in this note are polynomial
abbreviations, not additional variables. In particular, the rational
quantities used in the proof of the third construction do not occur in
its polynomial source.

The ordinary proof below composes with the retained package142/P66
calibration to finite syntactic ZFC refutations. It supplies no new
end-to-end Lean/Rocq certificate or encoded object-language ZFC proof.
It proves an equivalence of **zero existence**, not equality of all
coordinate-wise zero sets. No consistency assumption is used.

## 1. Common outer definitions and the exact constant interface

Use the four positive fixed integers `beta,K0,MC,MF` from the retained
`COEFFICIENT_BINDING.json`. Their finite reconstruction and exact byte
payloads accompany the source. In particular they satisfy

    beta >= 31, K0 > 0, 0 < MC < beta < MF < 2*beta.

Define

    q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, ell=E*k*Y, c=k*Y+eta, a=E+Y,
    a0=a+2, H=4*a+3, Delta=a*a+H=a0^2-1,
    D=X+a*c+gamma*H,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    N1=D^2-Delta*c^2,
    Nt=(K0+w)*C+(q-F)-z*(q-1),
    A=1+ell*(ell+k).

Here `A` is the first radicand; `a0` is the different main Pell base.
Always `q>=32`, `X>=q`, `Y>=q^3`, `E>=q^4`, `k>=2`, and
`c,A,Delta,D` are positive, with `A,Delta,c>1`.

The frozen parent equations additionally use `Nk=k-h*E-R`. The new
equations contain neither the variable `h` nor this factor. Recovering
its positive integer value is the central issue of this note.

Whenever `Nt=1`, positivity gives

    (K0+w)*C=1+z*(q-1)-(q-F) >= F > 0,

so `C>0`. Write `G0=(q-1)*(q-F)+alpha=q*alpha+(q-1)*C`.
Then `q<=G0<=q*(q-1)`, and the constant bounds imply

    0 < (MC+q*MF)*J < (2*q+1)*(q-1).

Consequently

    3*q < R < q^4-q^3+q^2-1 < q^4-2 <= E-2.       (1)

These bounds do not assume `Nk=1`, a dyadic identity, or any recovered
Pell index. They will therefore be available before the deleted quotient
is restored.

## 2. Two residue carriers with thirteen coordinates

The quantified coordinates are

    J,F,alpha,z,f,n,i,T,s,w,eta,zeta,gamma > 0.

Set the possibly signed polynomial carrier

    t0=E*n-k+R.                                  (2)

### 2.1 Raw form: 70 operations, degree 206

Define

    I=E*i*c^2,
    W=Delta*A*I^2,
    Q=Delta*W,
    Ns=f^2-W,
    V=f^2*(c*T-R)-c,
    B=Q*(t0^2-A*V^2)-t0^2+A.

The equation is

    P13r=N1*Nt*(3*B+1)*Ns-1=0.                   (3)

For gate sharing the literal source computes `I=(E*i)*c^2`,
`S0=(E*i)*(Delta*c^2)`, and `W=A*(I*S0)`.

### 2.2 Reduced form: 71 operations, degree 162

Instead define

    m=A*E*i, I=m*c^2, S=Delta*I,
    W=I*S,
    Ns=f^2-W,
    Q=Delta*(f^2-1),
    V=f^2*(c*T-R)-c,
    B=Q*(t0^2-A*V^2)-t0^2+A,
    P13d=N1*Nt*(3*B+1)*Ns-1.                     (4)

The old parent input `i` has been replaced by `E*i`. The three gates
for `Nk`, and its final product multiplication, disappear. Computing
`E*i` and the three-gate carrier (2) adds four gates. Therefore the
operation counts remain exactly those of the parent fourteen-variable
forms, namely 70 and 71. This construction removes a variable without
adding gates, at a moderate degree cost.

## 3. Unit recovery and the three Pell equations

At a zero of either (3) or (4), every displayed product factor is an
integer unit. Since `3*B+1=1 mod 3`, it is `+1`, hence `B=0`.
Also `Delta=0 or 3 mod 4`, so a norm `u^2-Delta*v^2` cannot be `-1`.
Thus `N1=1`.

In the raw form, write

    B=(Q-1)*t0^2-A*(Q*V^2-1)=0.                 (5)

The carrier `t0` is nonzero, since otherwise (5) gives `Q*V^2=1`,
impossible for the integer `Q>1`.
Since `A|Q`, both `Q-1` and `Q*V^2-1` are `-1 mod A`. For each
prime dividing `A`, its valuation in (5) is even. Therefore
`A=tau^2` for a positive integer `tau`, and `tau|t0`.
Now `W=Delta*(tau*I)^2`, so the same modulo-four argument excludes
`Ns=-1` and gives `Ns=1`.

In the reduced form, `W=Delta*I^2` before any extraction, so
`Ns=1` follows immediately. Hence `Q=S^2>1`. Since `A|S`, the
same nonzero-carrier observation and coprime valuation argument give
`A=tau^2` and `tau|t0`.

In either case the remaining unit is `Nt=1`; bounds (1) now hold.
Moreover `t0` cannot be zero: (5) would give `Q*V^2=1`, impossible
for the positive integer `Q>1`. Set `y=|t0|/tau>0`. Define the
normalized strong ordinate `Istar` by

    raw:     Istar=tau*E*i*c^2,
    reduced: Istar=A*E*i*c^2,
    Sstar=Delta*Istar.

The recovered equations are

    tau^2=1+ell*(ell+k),
    D^2-Delta*c^2=1,
    f^2-Delta*Istar^2=1,
    Q=Sstar^2,
    Sstar^2*V^2-(Sstar^2-1)*y^2=1.             (6)

We have both `c^2|Istar` and `E|Sstar`. The latter divisibility is
the purpose of scaling the free multiplier. No sign of `t0` or `V`
has been assumed.

## 4. Pell facts and signed main-index recovery

For an integer base `b>=2`, let

    chi_b(0)=1, chi_b(1)=b,
    psi_b(0)=0, psi_b(1)=1,
    z_(r+2)=2*b*z_(r+1)-z_r.

Equivalently `chi_b(r)+psi_b(r)*sqrt(b^2-1)` is the `r`th power of
`b+sqrt(b^2-1)`. We use the elementary addition identities, positive
Pell-solution classification, monotonicity, and strong divisibility
`gcd(psi_b(r),psi_b(s))=psi_b(gcd(r,s))`. They are retained in the
ordinary source audit. The signed-index argument below is also the
coefficient-independent argument in the retained incoming source
`universal_pell.tex`, Sections 3--4, including its Direct normalized
rank and Signed auxiliary-index recovery lemmas. It is reproduced
here to expose the hypotheses after removing `Nk`.

### 4.1 The first and main indices, before identifying either one

Put `v=E*Y=X*Y^2` and `P0=2*v+1`. The first equation in (6) is

    tau^2-v*(v+1)*k^2=1.

Its positive fundamental solution is `(2*v+1,2)`: at ordinate one,
`v^2+v+1` lies strictly between `v^2` and `(v+1)^2`. Therefore there
is an integer `r>=1` such that

    tau=chi_P0(r), k=2*psi_P0(r).                 (7)

Likewise `N1=1` gives a main index `p>=1` with

    D=chi_a0(p), c=psi_a0(p).                    (8)

If `r=1`, then `k=2`, `eta=zeta=1`, and `c=2*Y+1`; this is strictly
between `psi_a0(1)=1` and `psi_a0(2)=2*a0`, contradicting (8).
Thus `r>=2`. In particular

    k>=4*P0=8*X*Y^2+4,
    c>k*Y>8*X*Y^3>2*R.                         (9)

As `P0>a0`, equations (7)--(8) also imply `p>r>=2`. The growth
of `psi_a0` gives `c>2*p`. Thus `0<p,R<c/2` without using `Nk`.

### 4.2 Normalized rank

By the strong equation in (6), some `m>=1` satisfies
`f=chi_a0(m)` and `Istar=psi_a0(m)`. Since `c^2|Istar`, strong
divisibility implies `p|m`; write `m=p*u`. Composition gives

    Istar=c*psi_D(u), D=chi_a0(p), D^2=1 mod c.

The recurrence implies `psi_D(u)=u*D^(u-1) mod c`. As `D` is a
unit modulo `c`, divisibility by `c^2` forces `c|u`. Therefore

    p*c | m, c | m, m>=p*c>2*p.                 (10)

### 4.3 Signed abscissa step-down

For `0<j<m`, if

    chi_a0(t)=chi_a0(j) mod chi_a0(m),

then `t=+j or -j mod 2*m`. Indeed the addition identities give
`chi_a0(t+2*m)=-chi_a0(t)` and
`chi_a0(2*m-t)=-chi_a0(t)` modulo `chi_a0(m)`. Reduction and
reflection leave a signed `chi_a0(s)` with `0<=s<=m`.
The endpoint `s=m` has residue zero. A negative representative cannot
equal `chi_a0(j)`, since

    0<chi_a0(s)+chi_a0(j)<=2*chi_a0(m-1)<chi_a0(m)

when `s<m`. For a positive representative, strict monotonicity forces
`s=j`. The index operations give the claimed signed congruence.

### 4.4 Odd quotient polynomials and recovery of p=R

There are integer polynomials `L_u` with

    L_0(Z)=1, L_1(Z)=4*Z-3,
    L_(u+1)(Z)=(4*Z-2)*L_u(Z)-L_(u-1)(Z),
    chi_b(2*u+1)=b*L_u(b^2),
    L_u(0)=(-1)^u*(2*u+1),
    L_u(1-a0^2)=(-1)^u*psi_a0(2*u+1).           (11)

These are immediate inductions using the recurrence. The odd ordinate
recurrence also gives

    psi_b(2*u+1)=(-1)^u mod 4*b^2.              (12)

The last equation of (6) excludes zero values of `V,y`. Positive
Pell classification gives an index `nu>=1` with

    Sstar*|V|=chi_Sstar(nu), y=psi_Sstar(nu).

The index is odd, since `chi_Sstar(2*u)=(-1)^u mod Sstar`, whereas
the left side is divisible by `Sstar`. Write `nu=2*u+1`.
Then `|V|=L_u(Q)`. On the other hand, definitions and (6) give

    Q=Delta*(f^2-1)=1-a0^2 mod f,
    V=-c mod f,
    Q=0 mod c,
    V=-R mod c.                                (13)

Equations (11)--(13), with either sign of `V`, imply
`psi_a0(nu)=+c or -c mod f`. Squaring and using
`chi_a0(2*j)=1+2*Delta*psi_a0(j)^2` gives

    chi_a0(2*nu)=chi_a0(2*p) mod chi_a0(m).

The step-down result applies since `2*p<m`; hence
`nu=+p or -p mod m`, and therefore modulo `c`. Reduction of (11)
at zero, using (13), gives `nu=+R or -R mod c`. Thus
`p=+R or -R mod c`. Since both `p,R` lie strictly between zero
and `c/2`, the only possibility is

    p=R.                                       (14)

This deduction has not used a deleted quotient, a main-root congruence,
or an assumed positive sign of `V`.

## 5. Reading the deleted quotient from the auxiliary ordinate

First, the recurrence at base `P0=1 mod E` gives

    tau=1 mod E, k=2*r mod E.                   (15)

Second, (12), `E|Sstar`, and oddness of `nu` give `y=+1 or -1 mod E`.
Since `t0=+tau*y or -tau*y`, equations (2) and (15) imply

    k-R=epsilon mod E, epsilon in {+1,-1}.

Thus `E|(2*r-R-epsilon)`. We already know `1<=r<p=R` and `R<E`.
Consequently `|2*r-R-epsilon|<R<E`, so

    2*r=R+epsilon.                             (16)

The negative sign is impossible. If `epsilon=-1`, then `R=2*r+1`.
Set `B0=2*a0^2-1>P0`. The even-index composition identity gives

    psi_a0(2*r)=2*a0*psi_B0(r)
                >=2*a0*psi_P0(r)
                =a0*k>k*(Y+1).

But then `c=psi_a0(R)>k*(Y+1)`, contrary to
`c=k*Y+eta<k*(Y+1)` because `eta<k`. Hence `epsilon=+1` and

    k-R-1=0 mod E.

This difference is strictly positive: `r>=2` and (9) give
`k>=8*X*Y^2+4>R+1`. Restore

    h=(k-R-1)/E > 0.                            (17)

All entries of the frozen fourteen-variable parent are now positive
integers: use its multiplier `i_parent=E*i`, its carrier variable
`t_parent=|t0|`, and (17). Every parent product factor is `+1`.
Thus a zero of either new thirteen-variable equation yields an exact
positive parent zero and hence a finite syntactic ZFC refutation.

## 6. Completeness of the residue carriers

A finite refutation supplies canonical outer data from the retained
P66 calibration, with

    A=tau^2, c=psi_a0(R), R=3 mod 4,
    N1=Nt=Nk=1.

The finite matrix-period argument in package142, PROOF Section 4, lets
the normalized strong multiplier `j` be any sufficiently large member
of a cofinal family divisible by a prescribed positive integer.
Choose it divisible by `tau*E` for the raw form, or by `A*E` for the
reduced form, and set respectively

    i=j/(tau*E), or i=j/(A*E).

Then `f^2=1+Delta*j^2*c^4` and `Sstar=Delta*j*c^2` is divisible by
`E`. Choose fresh auxiliary witnesses for this strong pair:

    Vstar=chi_Sstar(R)/Sstar,
    ystar=psi_Sstar(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2).

The quotient polynomials (11) and `R=3 mod 4` give
`Vstar=-c mod f^2` and `Vstar=-R mod c`. As `f^2=1 mod c` and
`gcd(f,c)=1`, `Tstar` is a positive integer. The auxiliary norm holds.
Equation (12) gives `ystar=-1 mod E`; also `tau=1 mod E`.
Put `tstar=tau*ystar>0`. As `k-R=h*E+1`, the value

    n=(tstar+k-R)/E

is a positive integer. Then (2) equals `tstar`, all new factors are
`+1`, and the new equation has a zero. The fresh choice of auxiliary
witnesses after altering the strong multiplier is essential; no old
private auxiliary values are claimed to persist.

### 6.1 Smaller modulus: thirteen coordinates, 72 operations, degree 154

The residue only has to be read modulo an integer larger than `R`.
It need not be the whole modulus `E`. This gives a fourth construction:
in the reduced form (4), replace exactly

    t0=q^4*n-k+R,
    m=A*q^2*i.

Keep every other definition and the same product `N1*Nt*(3*B+1)*Ns-1`.
The complete source is `fixed_13_residue_q4_72_degree154.json`.
The existing register `q2=q^2` scales the multiplier; one extra squaring
computes `q^4`. The gate count is 72, comprising 41 multiplications,
18 additions, and 13 subtractions.

Sections 3--4 apply with `Istar=A*q^2*i*c^2`, giving the main index
`p=R`, first index `1<r<R`, and `Q=Sstar^2`. Now `q^4|Q`, which is
sufficient for (12) to give `y=+1 or -1 mod q^4`. Also
`P0=1 mod q^4`, so `tau=1 mod q^4` and `k=2*r mod q^4`.
Since `R<q^4`, the argument of Section 5 yields `2*r=R+epsilon`.
The same growth comparison excludes `epsilon=-1`; therefore
`2*r=R+1`. Finally the full first recurrence, before reducing its
modulus, gives

    k=2*psi_P0(r)=2*r mod 2*(P0-1)=4*E*Y.

In particular `E|(k-R-1)`. Its positivity and the restoration of `h`
are exactly as before. The parent multiplier is `q^2*i`.

Conversely choose a canonical normalized strong multiplier divisible
by `A*q^2` and take `i=j/(A*q^2)`. Then `q^4|Q`, and the fresh
canonical auxiliary ordinate is `-1 mod q^4`. As `tau=1 mod q^4`
and `k-R=1 mod E`, with `q^4|E`,

    n=(tau*ystar+k-R)/q^4

is a positive integer. This gives completeness. No weaker congruence
has been silently substituted for the original deleted condition;
the exact first index recovers its full modulus afterwards.

## 7. A rational carrier with twelve positive coordinates

The quantified coordinates are

    J,F,alpha,z,n,i,T,s,w,eta,zeta,gamma > 0.

Use the common outer definitions and set

    m=a0*D*i, I=m*c^2,
    W=Delta*A*I^2, F2=1+W, Q=Delta*W, G=A*F2,
    V=F2*(c*T-R)-c,
    e=k-R-1, Z=E*n+e,
    B12=Q*(Z^2-E^2*G*V^2)-Z^2+E^2*G,
    P12=N1*Nt*(3*B12+1)-1.                     (18)

This is an ordinary polynomial with 74 binary operations and exact
degree 438. Its graph is the literal anchored parent with `Nk`
removed and with the rational substitution `t=n+e/E` cleared by
`E^2`. There is no division in (18).

### 7.1 Rational adjacent-Pell integrality

This is an inherited lemma, already used in the retained denominator
projection proofs, including `fixed_sources/adjacent_pell_predecessor.md`,
Section 2. We reproduce its short proof to make the present application
self-contained. The contribution here is its application to the anchored
72-operation equation with `t=n+(k-R-1)/E`, not the lemma itself.

**Lemma.** If integers `Q>=2,V` and a rational number `y` satisfy

    Q*V^2-(Q-1)*y^2=1,

then `y` is an integer.

**Proof.** Replace `V,y` by their absolute values. The equation
excludes zero values, so write `v=|V|>=1` and `y=b/d>0` in lowest
terms. With `D0=Q-1`, the equation implies `d^2|D0`.
If `v=1`, then `y=1`. Otherwise `y>v`. Define

    v'=(2*Q-1)*v-2*D0*y,
    y'=|(2*Q-1)*y-2*Q*v|.

The first coordinate is an integer because `d|D0`. Moreover

    ((2*Q-1)*v)^2-(2*D0*y)^2=v^2+4*D0>0,

so `0<v'<v`. The same norm identity holds for `(v',y')`, by direct
expansion. The reduced denominator of `y'` is still exactly `d`:
`2*Q-1=1 mod d`, so its numerator is a unit modulo every prime
dividing `d`. Descent in the positive integer `v` reaches `v=1`,
where the denominator is one. Hence `d=1`. QED.

### 7.2 Soundness of the twelve-variable equation

The unit arguments give `N1=Nt=1` and `B12=0`; therefore (1) holds.
Since `n>=1` and `e=k-R-1>=1-R>-E`, one has `Z>0`. The positive
rational number `t=Z/E` satisfies

    (Q-1)*t^2=A*F2*(Q*V^2-1).                  (19)

The anchored parent's coprimalities remain valid:

    gcd(A,F2*(Q-1)*(Q*V^2-1))=1,
    gcd(F2,Q-1)=gcd(F2,Q*V^2-1)=1.              (20)

For completeness, `A|Q` and `F2=1 mod A` give the first statement.
Also `Q-1=Delta*F2-a0^2`, while `F2=1 mod a0`, giving the second.
Finally `V=-c mod F2`, so
`Q*V^2-1=-Delta*c^2-1=-D^2 mod F2`, using `N1=1`.
Since `F2=1 mod D`, the last coprimality follows.

For a prime dividing `A` or `F2`, valuation in (19) and (20) shows
that its exponent in that factor is even. This reasoning is valid
for rational `t`: its prime valuations are integers and twice such
a valuation is even. Thus `A=tau^2` and `F2=f^2` for positive
integers `tau,f`. Now

    Q=(Delta*tau*m*c^2)^2>1,
    y=t/(tau*f)>0,
    Q*V^2-(Q-1)*y^2=1.

The preceding lemma forces `y` to be an integer. Hence `t=tau*f*y`
is an integer, and `E|e`. The bounds `e>-E` imply `e>=0`.
If `e=0`, then `k=R+1`; classification of the first Pell equation
gives either `k=2` or `k>=8*X*Y^2+4`. Both conflict with
`3*q<R<q^4-2`. Therefore `e>0` and `h=e/E>0`.

Restoring this `h` and the positive integer `t` gives an exact zero
of the frozen anchored thirteen-variable parent. This proves soundness
without any mixed-sign inference about square roots of one modulo `E`.

### 7.3 Completeness

Choose canonical outer data of a refutation, so `e=h*E` with `h>0`.
The anchored parent's finite matrix-period completion can choose
arbitrarily large strong multipliers divisible by `tau*a0*D`.
Its parameterized powers are unbounded, and each fresh auxiliary
completion has `t=tau*f*y>=f`; hence choose one with `t>h`.
Set `n=t-h>0`. Then `Z=E*t`, and (18) is `E^2` times the parent's
zero auxiliary residual, with the already-unit `Nk` deleted.
All new factors are one. Thus (18) has a positive zero whenever
a finite ZFC refutation exists.

The same-cost residue argument for the thirteen-variable forms does
**not** automatically extend to this anchored case: here `t=tau*f*y`,
and a square root `f^2=1 mod E` can have mixed Chinese-remainder
signs. The rational-carrier proof above avoids that unsupported step.

## 8. Exact degrees and nonzero leading coefficients

Give each positive coordinate degree one and fixed integer leaves
degree zero. Put

    q0=beta*J, k0=eta+zeta,
    e0=w*s*q0^4, c0=k0*s*q0^3,
    A0=(w*s^2*k0*q0^7)^2,
    Lt=w*(q0-F-alpha)-z*q0.

The exact cancellation

    N1=2*a*c*(X+gamma*H)+(X+gamma*H)^2-H*c^2

gives degree 18 and leading part `8*gamma*e0^2*c0`. The degree-two
leading part of `Nt` is `Lt`.

For (3), the degrees of `W,Q,V,B,Ns` are `68,80,8,118,68`.
The complete degree-206 homogeneous part is

    24*gamma*i^4*A0^3*e0^12*c0^11*f^4*T^2*Lt.

Its monomial

    J^124*w^18*s^35*eta^17*i^4*f^4*T^2*gamma*z

has coefficient `-24*beta^124`, which is nonzero at the actual tuple.

For (4), these degrees are `90,14,8,52,90`; the complete degree-162
homogeneous part is

    24*gamma*i^2*A0^3*e0^8*c0^7*f^6*T^2*Lt.

Its monomial

    J^96*w^14*s^27*eta^13*i^2*f^6*T^2*gamma*z

has coefficient `-24*beta^96`.

For the `q^4` reduced carrier, the degrees of `W,Q,V,B,Ns` are
`82,14,8,52,82`. Its complete degree-154 homogeneous part is

    24*gamma*i^2*A0^3*e0^6*c0^7*f^6*T^2*q0^4*Lt.

The monomial

    J^92*w^12*s^25*eta^13*i^2*f^6*T^2*gamma*z

has coefficient `-24*beta^92`.

For (18), the degrees of `W,Q,G,V,B12` are `90,102,112,96,418`.
The complete degree-438 homogeneous part is

    -24*gamma*i^8*A0^5*e0^30*c0^27*T^2*Lt.

Its monomial

    J^272*w^40*s^77*eta^37*i^8*T^2*gamma*z

has coefficient `+24*beta^272`. All four degrees are therefore
attained for the fixed coefficient tuple, not merely syntactic bounds.

## 9. Logical conclusion and scope of the contribution

For each of the four explicit integer polynomials above, the two
existence maps and the retained exact calibration prove, by ordinary
mathematics formalizable in ZFC,

    (there is no strictly positive integer zero) <=> Con(ZFC).

The residue carriers eliminate the index quotient by making the
auxiliary Pell ordinate carry its residue. The rational carrier uses
automatic integrality of an adjacent-coefficient Pell ordinate to
remove the same quotient at a smaller variable count. The operation
and degree figures are literal, reproducible properties of the complete
fixed sources. No global minimum or historical priority is claimed;
comparisons must be made with the specified repository snapshot and
with matching variable domain, gate model, and coefficient accounting.
