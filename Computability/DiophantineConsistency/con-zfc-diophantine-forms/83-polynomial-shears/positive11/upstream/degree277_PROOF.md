# Pell descent removes the denominator guard from the eleven-variable equation

## Result, novelty scope, and fixed source

At ProveIt commit `2605669a532342f153b13eb6b4a0af4b54f5fa37`, package 70's
eleven-positive-variable polynomial has exact degree 325 and 113 binary
arithmetic operations. The equation here has **eleven strictly positive
integer unknowns, exact degree 277, and 111 operations**. Its two-residual
system has 108 operations. This is a proved improvement to that particular
frontier, with a 14.77% degree reduction, not a reduction below the existing
nine-positive variable count or a global optimality assertion.

The construction combines package 70's three-root transfer with package 69's
rational Pell descent. Neither ingredient is claimed as new in isolation.
The new observation is that the latter makes the former's factor `q(q-1)`
completely unnecessary. That factor appears in the strong Pell ordinate,
and removing it saves degree at every subsequent norm level.

The four fixed integer coefficients are exactly package 44's whole compact
tuple, as used by package 70: `beta=2^590069-1`, `K0`, `MC`, and the **already
shifted** `MF`. Their actual compressed integer bytes are retained in
`coefficients/`, with a coherent whole-tuple identity and SHA256 receipts.
They are coefficients, not unknowns. No coefficient is selected according
to whether ZFC is consistent. The native K215/refutation calibration and
the positive Pell interface are inherited ordinary mathematical results.
This package does not claim a new end-to-end proof-assistant certificate
or an object-language ZFC derivation.

## 1. Complete division-free equation

The ordered positive unknowns are

    j,F,alpha,i,T,X,Y,n,eta,zeta,gamma.

All following names are polynomial abbreviations, not additional variables:

    J=3j+1, q=beta J+1, C=q-F-alpha, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1, ell=EkY,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Rhat=q^3(q+F+alpha), M=q^3(q-1),
    Bt=(q K0+X)C-qF, Dtau=ell(ell+k)+1,
    I=i c^2, Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
    V=Df(cT-R)-c, Dnum=Q V^2-1,
    Vbar=Df(cT+Rhat), L=3 Vbar, W=1+(q-1)L,
    Zbar=M(ell+k+n+L)+(q-1)Y-q^3 W Bt,
    r0=k-R-1, S=4qY, U=qS,
    Dstar=U(X+ac)+H(U gamma+SX-r0),
    A1=Dstar^2-U^2(1+Delta c^2),
    A=M^2 Dtau, Bf=M^2 Df, Cnum=M^2 Dnum,
    Tn=delta^2 A Bf, Rn=delta Cnum,
    Jn=delta(Zbar^2-A-Bf)-Cnum,
    Ncenter=Jn^2-4[Tn+Rn(A+Bf)],
    N8=Ncenter^2-64 Tn Rn Zbar^2.

The single polynomial equation is

    P11=N8+A1+N8 A1=0.

All powers are fixed nonnegative integers. The literal arithmetic DAG is
`p11_positive_degree277.json`; `build.py` reproduces its exact bytes.

The only mathematical change to package 70 is

    old I=i q(q-1)c^2  -->  new I=i c^2.

Two multiplication gates disappear. All other named register formulas
are identical after that replacement.

## 2. Universal rational-integrality lemma

**Lemma.** Let `Q>1` be an integer, let `V` be an integer, and let `y` be
rational. If

    Q V^2-(Q-1)y^2=1,

then `y` is an integer.

**Proof.** Signs can be changed independently, so assume `V>0,y>0`.
Neither coordinate can be zero: if `V=0`, the left side is nonpositive;
if `y=0`, it would give `Q V^2=1`. Write `y=a/m` in lowest terms with
`m>0`. The equation implies `m^2` divides `Q-1`, hence `m` divides `Q-1`.

For `V=1`, the norm gives `y=1` and `m=1`. For `V>1`, set

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The first is an integer because `m|(Q-1)`. Direct expansion shows

    Q(V')^2-(Q-1)(y')^2=QV^2-(Q-1)y^2=1.

From `(Q-1)(y^2-V^2)=V^2-1>0` we have `y>V`. Also `QV>(Q-1)y`,
since the difference of their squared values is `QV^2+Q-1>0`.
Together these imply `-V<V'<V`. The new norm excludes `V'=0`.

The reduced denominator of `y'` is exactly `m`: `2Q-1` is congruent
to 1 modulo `m`, and the other term is integral. Replacing `V',y'`
by their absolute values therefore produces a strictly smaller positive
integer first coordinate with the same denominator. Strong induction
reaches `V=1`, proving `m=1`. This proof handles all initial signs and
requires neither a positivity condition on `V` nor any external
divisibility modulus. QED.

This is package 69's lemma. It is repeated in full because it removes the
only use of the deleted factor in package 70's soundness proof.

## 3. Radical separation survives unchanged

The following estimates hold for every positive input tuple, before any
equation is imposed. In particular, they do not assume `C>0` or recover
any native index prematurely. Because `i>=1`, the new ordinate still has
`I>=c^2`, which is all these estimates need.

We have `q>=16,k>=2,c>=3,a>=2,Delta>=15`, and

    ell<ac, k<c, 1<Dtau<Df<Q.

Writing `t=sqrt(Dtau)` and `f=sqrt(Df)`,

    t<ell+k<(a+1)c,
    f>(a+1)I >= (a+1)c^2 >= 3c^2.

Put `b=cT-R`, so `V=Df b-c`. If `b=0`, then `V=-c`; if `b!=0`,
then `|V|>=Df-c>1`. Thus `|V|>1` in all cases, and the rational number

    Dy=(Q V^2-1)/(Q-1)
      =V^2+(V^2-1)/(Q-1)

is positive and greater than 1. Set `y=sqrt(Dy)>0`.

The three radicands `Dtau,Df,Dy` are pairwise distinct. Indeed `Dtau<Df`;
if `Dy` were either of the first two integers `D`, then
`Q(D-V^2)=D-1` with `0<D-1<Q`, which is impossible.

If `b=0`, then `Q>c^2` gives `y<c+1`, whereas
`f-t>(a+1)c(c-1)>c+1`. Thus `f>t+y`.
If `b!=0`, then `y>|V|>=Df-c>2f>f+t`.
Consequently no signed sum of the three positive roots is zero.

The fixed native mask bounds `0<MC<beta`, `0<MF<2beta` give

    |R| < q^4+Fq^3+(alpha+2)q^2 < q^3(q+F+alpha)=Rhat.

The integer difference `Rhat-|R|` is at least 1, and `Df>c`, so
`|V|<Df(cT+Rhat)=Vbar`. Since `Q-1>1`, we have `y<2|V|` and
`f<Vbar`. Hence the unchanged positive majorant satisfies

    L=3 Vbar>f+y,  L>k.

## 4. Recover the signed roots

The universal identity

    F8(z;a,b,c)
      =[(z^2-a-b-c)^2-4(ab+ac+bc)]^2-64abc z^2
      =product_(eps in {+1,-1}^3)
         (z-eps1 sqrt(a)-eps2 sqrt(b)-eps3 sqrt(c))

is checked as an exact polynomial identity. Here `N8` is precisely
`delta^4 F8(Zbar; M^2 Dtau,M^2 Df,M^2 Dy)`.
Thus `N8=0` yields signed roots `tau*,f*,y*` with

    Zbar/M=tau*+f*+y*,
    (tau*)^2=Dtau, (f*)^2=Df, (y*)^2=Dy.

All three are rational. For completeness, the general three-root argument
is as follows. If signed roots `x1,x2,x3` of pairwise distinct positive
rationals `a,b,c` have nonzero rational sum `s`, put

    u=(s^2-a-b-c)/2, v=(u^2-ab-ac-bc)/(2s).

Then `u=x1x2+x1x3+x2x3`, `v=x1x2x3`, and

    x1=a(a+u)/(a s+v),
    a s+v=x1(x1+x2)(x1+x3).

The denominator is nonzero because the radicands are pairwise distinct.
The other roots follow cyclically. Section 3 supplies the nonzero sum
and distinctness hypotheses.

Since `Dtau,Df` are integers, their rational square roots `tau*,f*`
are integers. At this point `V,Q` were already integers, independently
of root recovery, and the auxiliary root satisfies

    QV^2-(Q-1)(y*)^2=1.

The lemma of Section 2 now gives `y*` integral. Package 70 instead used
`gcd(M,Q-1)=1`, obtained from `q(q-1)|I`. That condition has disappeared
entirely; no proof step needs it.

## 5. Soundness via the inherited positive Pell interface

Use the weighted interface established by package 70's positive component
(retained `upstream/70-residue-orientation__positive__section.tex`). It
allows any positive weight `hstar`; its canonical completeness allows any
such `hstar>=k`. Its four residuals are the first carrier norm, the adaptive
main carrier norm, the normalized strong Pell equation, and the auxiliary
Pell equation.

From a zero with `N8=A1=0`, restore

    i_old=i, f_old=|f*|, y_old=|y*|,
    u=y_old-V,
    r=n+L-f*-y*, hstar=L.

These restored coordinates are integers. Section 3 implies `y_old>|V|`,
so `u>0`; it also gives `L>|f*|+|y*|`, so `r>0`. The signed roots,
not their absolute values, are used in `r`. The equations imply

    f_old^2-Delta(i_old c^2)^2=1,
    y_old^2-Q(y_old^2-V^2)=1,
    Zbar-M(f*+y*)=M tau*.

The last equation is exactly the first transport carrier with the restored
`r`, and the main residual is `A1=0`. Thus all four residuals of the
inherited interface vanish on positive witnesses. The source's ordinary
soundness theorem produces a finite refutation in the fixed ZFC proof
calculus. This argument uses the literal whole coefficient tuple.

## 6. Completeness

A finite refutation gives the canonical source tuple from the inherited
native and Pell construction. It has `q>=16`, `R=3 mod4`,
`c=psi_(a+2)(R)`, and a positive source transport quotient satisfying

    t_source=Bt/(q-1)=q(z_source-1)>=q,
    s=Y/q^3<k, ell<tau<ell+k.

Choose a positive Pell solution `f,I` with `c^2|I`. One may simply use
the normalized source choice. Independently, existence follows by reducing
the determinant-one Pell matrix

    [[a+2,Delta],[1,a+2]]

modulo `c^2` and taking a positive power equal to the identity. Its
lower-left entry is a positive Pell ordinate divisible by `c^2`. Put
`i=I/c^2>0`.

The canonical auxiliary reconstruction, retained from package 61's signed
index lemma, gives positive `T,u` and `y=V+u`, for this choice of strong
Pell pair. It only needs `c|I`, which holds. Compute `Vbar,L,W` afterward,
avoiding any dependence loop. Set

    r=Wt_source+tau-ell-k-s.

Then `r>qW-2k>L`, using `q>=16` and `L>=k`. Therefore

    n=r-L+f+y>0.

All eleven new inputs are positive. Direct substitution gives
`Zbar=M(tau+f+y)`, hence `N8=0`; the weighted main carrier supplies the
same positive `gamma` and `A1=0`. This proves completeness.

## 7. The one-equation finalizer

For all integer inputs, `N8` is a square modulo 4, because its subtracted
term has coefficient 64. Also `A1` is a square modulo 4 since `4|U`.
If `(1+N8)(1+A1)=1`, both factors are units in the integers. The negative
case would force `N8=A1=-2`, impossible modulo 4. Therefore

    P11=0  iff  N8=A1=0.

The two existence implications establish, by ordinary arguments
formalizable in ZFC and the explicitly inherited calibration,

    ZFC proves: (there is no positive integer zero of P11) iff Con(ZFC).

This is an equivalence, not a proof that either side holds. Full native
calibration in the proof assistant and internal ZFC syntax/proof transport
remain the repository's separate formalization obligations.

## 8. Exact degree and circuit certificate

With each input assigned degree 1 and fixed coefficients degree 0, the
exact register degrees are

| Register | I | Df | Q | V,L | Zbar | A | Bf | Cnum | Ncenter | N8 | A1 | P11 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Degree | 5 | 14 | 18 | 18 | 24 | 16 | 22 | 62 | 132 | 264 | 13 | 277 |

The apparent degree-14 leading terms of the main Pell residual cancel.
This is certified by the identity, with `Dtail=UX+H shift`,

    (Uac+Dtail)^2-U^2(1+(a^2+H)c^2)
      =2Uac Dtail+Dtail^2-U^2Hc^2-U^2.

All later leading terms are unambiguous. Put `q0=3 beta j`, `k0=eta+zeta`,
and

    Bt0=(K0 q0+X)(q0-F-alpha)-q0 F,
    Q0=i^2 k0^4 X^4 Y^8,
    L0=3i^2 k0^4 X^2 Y^6 q0^3(q0+F+alpha),
    Z0=-q0^4 L0 Bt0,
    A10=32q0^2 k0 X^2Y^4[4q0^2Y gamma+q0^3(q0-F)].

The degree-277 leading form of `P11` is exactly `Q0^4 Z0^8 A10`.
The coefficient of

    j^60 i^24 eta^49 X^42 Y^85 alpha^16 gamma

is `2^7*3^8*(3 beta)^60`, strictly positive on the authentic fixed
coefficient slice. It cannot cancel by any specialization of the other
three coefficient ports. This proves exact, not merely upper-bound,
degree 277.

The DAG has 65 multiplications, 29 additions, and 17 subtractions. Every
binary arithmetic operation is charged, including squares and scalar
multiplication. Register reuse and fixed numeral leaves are free. These
are circuit costs, not bit-operation or expanded coefficient-size costs.

## 9. Reproduction and attribution

Run `python3 verify.py` and `python3 -O verify.py`. The scripts verify the
complete literal DAG, all named register identities, eight-conjugate norm,
radical extraction formulas, main degree cancellation, exact leading
forms, selected coefficient, liveness, gate count, the descent's norm
identity, source identities, and actual coefficient bytes. The small
Pell examples are labeled diagnostics; the induction of Section 2 is
the universal proof.

The builder and exact sparse-ring audit are adapted from package 70 and
retain attribution and licensing. The new proof is a composition of
package 69's rational-integrality lemma with package 70's root transfer.
It is not a newly invented universal compiler, machine-free encoding,
global minimality theorem, or proof that Con(ZFC) is true.
