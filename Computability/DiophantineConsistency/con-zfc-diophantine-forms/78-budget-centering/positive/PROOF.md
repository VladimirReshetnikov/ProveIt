# Removing an unnecessary divisibility guard from three-root transport

## Scope and provenance

This component gives two explicit fixed-coefficient integer polynomials:

| Domain | Unknowns | Exact degree | Live binary operations |
|---|---:|---:|---:|
| Strictly positive integers | 11 | 277 | 111 |
| Strictly positive integers | 12 | 78 | 103 |

Their ordinary mathematical proofs establish, over the same syntactic proof
predicate as the upstream native compiler, that existence of a positive zero
is equivalent to the existence of a finite ZFC refutation. Negating gives the
requested ZFC-provable equivalence with Con(ZFC). This is an inherited-source
construction, not a new end-to-end Lean/Rocq formalization or a claim of global
minimality. It still uses the native K215 compiler. The contribution is the
specific composition of independent wave-10 mechanisms.

Source snapshot: ProveIt commit
`2605669a532342f153b13eb6b4a0af4b54f5fa37` (the relevant files are also present
at wave-10 reconciliation `cf4a5218a5a4e4358d3f5314151b6b05d4aa384e`).

* The eleven-positive base is source 70, `70-residue-orientation/eleven/PROOF.md`.
* The adjacent-coefficient rational-integrality theorem is source 69,
  `69-cones-pell/positive/PROOF.md`, Section 2.
* The twelve-positive norm merger is source 69, the same proof, Sections 3--5.
* The adaptive main carrier is source 70 and source 72,
  `72-congruence-sextic/positive13/PROOF13.md`, Section 6.

The unmodified first two source proofs are included in `upstream/`. Source
69's descent lemma is credited to that source; it is not claimed as new here.
The complete compact44 coefficient tuple is included in `coefficients/`.
Its four integer ports are beta,K0,MC,MF, with beta=2^590069-1 and MF already
shifted. The raw and compressed hashes and the whole-tuple binding are checked.

## 1. The arithmetic lemma that makes the change possible

Let Q>1 and V be integers. If y is rational and

    Q V^2 - (Q-1)y^2 = 1,

then y is an integer.

Here is a self-contained proof, reproduced with attribution to source 69.
Write y=a/m in lowest terms, m>0. The equation implies m^2 divides Q-1.
It excludes V=0 and y=0. Change signs to make V,y positive. If V=1 then
y=1. If V>1, set

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The first expression is integral, the norm is unchanged, and the reduced
denominator of y' is exactly m because 2Q-1 is 1 modulo m. Since

    y>V,   QV>(Q-1)y,

one has -V<V'<V. The equation excludes V'=0. Replacing V',y' by absolute
values and using strong induction on V reaches V=1 without changing m.
Thus m=1. The determinant-one polynomial identity used here is checked
exactly in `twelve/verify.py`.

## 2. Eleven-positive-variable equation

Take every register and the final polynomial from source 70's eleven-positive
construction, reproduced in `upstream/PROOF11_original.md`, with one change:

    old: I=i q(q-1)c^2,
    new: I=i c^2.

All eleven supplied unknowns remain strictly positive:

    j,F,alpha,i,T,X,Y,n,eta,zeta,gamma.

The exact final polynomial remains

    P11=(1+N8)(1+A1)-1,

where, with the other registers unchanged,

    Df=1+Delta I^2,
    Q=Delta(Df-1), delta=Q-1,
    V=Df(cT-R)-c,
    A=M^2 Dtau, Bf=M^2 Df, Cnum=M^2(QV^2-1),
    Ncenter=delta^2[(Zbar^2-A-Bf)^2-4ABf]
            -2delta Cnum(Zbar^2+A+Bf)+Cnum^2,
    N8=Ncenter^2-64delta^3 A Bf Cnum Zbar^2.

`eleven/p11_positive_degree277.json` is a complete division-free DAG, and
`eleven/build.py` rebuilds it. The register definitions in the original proof
plus the single replacement above also specify the entire polynomial.

### Soundness

The source proof's unconditional inequalities use only I>=c^2, not the extra
q(q-1) factor. In particular its three positive radicands Dtau,Df,Dy are
distinct, where

    Dy=(QV^2-1)/(Q-1),

and no signed sum of their roots is zero. The same octic norm equation
therefore gives rational signed roots tau_*, f_*, y_*. Rational-square
integrality makes tau_* and f_* integers. The displayed adjacent-coefficient
lemma now makes y_* an integer, without any condition on gcd(M,Q-1).

This replaces the entire old prime-support argument, which was the only use
of the extra q(q-1) factor. The other recovery formulas are unchanged:

    f_old=|f_*|, y_old=|y_*|,
    u=y_old-V>0,
    r=n+L-f_*-y_*>0.

The strong ordinate is I=i c^2 and already has the divisibility required by
the normalized source theorem. Hence the weighted four-residual source
interface is recovered and yields a finite syntactic ZFC refutation. The
signed roots, not their absolute values, must be used in the formula for r.

The finalizer proof is unchanged: N8 and A1 are squares modulo 4. Thus a
zero of (1+N8)(1+A1)-1 forces both residuals to be zero; the alternative
factor value -1 would require a residual congruent to 2 modulo 4.

### Completeness

There is an especially simple direct map from the old equation to the new
one. Given any old positive zero, set

    i_new=q(q-1)i_old

and retain every other supplied coordinate. This preserves the value of I
and consequently every downstream register. The new tuple is positive and
has the same zero polynomial value. The already-proved completeness of
source 70 therefore supplies completeness here, without any new cofinality
or Pell-index choice.

### Exact degree

The changed register degrees are

    I:5, Df:14, Q:18, V:18, L:18, W:19, Zbar:24,
    A:16, Bf:22, Cnum:62, Ncenter:132, N8:264, A1:13.

The unique leading term of N8 is Q_0^4 Zbar_0^8. Put

    q0=3 beta j, k0=eta+zeta,
    Bt0=(K0 q0+X)(q0-F-alpha)-q0 F.

Then

    Q0=i^2 k0^4 X^4 Y^8,
    Zbar0=-3i^2 q0^7 k0^4 X^2 Y^6(q0+F+alpha)Bt0,
    (A1)13=32q0^2 k0 X^2Y^4[4q0^2Y gamma+q0^3(q0-F)].

The coefficient of

    j^60 i^24 eta^49 X^42 Y^85 alpha^16 gamma

in P11 is 2^7*3^8*(3 beta)^60, which is nonzero for the actual beta.
Its total degree is 277. This proves exact degree after specialization to
the authentic coefficients, not just a formal degree upper bound.

The literal evaluator has 111 live gates: 65 multiplications, 29 additions,
17 subtractions. This removes two gates from source 70's 113-gate evaluator.

## 3. Twelve-positive-variable equation

Take source 69's twelve-positive-variable equation, reproduced in
`upstream/PROOF12_original.md`. Keep J=6j+1, q=beta J+1 and every register
except the main carrier. Replace

    U=q^5, Dstar=U(X+ac)+H[U gamma+q^4X-(k-R-1)]

with

    S=4qY, U=qS=4q^2Y,
    Dstar=U(X+ac)+H[U gamma+SX-(k-R-1)].

The main residual is still

    A1=Dstar^2-U^2(1+Delta c^2).

The first residual A0 and the two-root resultant N are unchanged. Thus

    P12=(1+A0)(1+A1)(1+N)-1.

`twelve/equation.json` is the full division-free definition. The unknowns
are j,F,alpha,t,T,X,Y,r,eta,zeta,n,gamma, all strictly positive.

### Soundness in the correct order

As in source 69, the finalizer implies A0=A1=N=0: q is even, U is a
multiple of 4, and every residual is a square modulo 4. A0 first gives
q^3|Y and C=q-F-alpha>0. These give q>=16, q=2 modulo 3, and
3q<R<q^4-2. The new Dstar is positive because

    Dstar > Uac-Hk > ak(UY-5)>0.

Thus A1 recovers an integer positive main Pell root. Its existence and
the first Pell root imply c>2R, by exactly the source 69 first-index
argument. Hence V=(t+1)^2(cT-R)-c>1. Source 69's unchanged resultant
and the arithmetic lemma above recover positive integral strong and
auxiliary coordinates. The signed auxiliary-index theorem then gives p=R.

It remains to check the altered adaptive main modulus. With

    mu=S/gcd(S,H),

q^3|Y, q=2 modulo 3 and H=4Y(X+1)+3 imply gcd(S,H)<=3. Thus
mu>=4qY/3>q^4>R+1. Also S and U divide 4XY^2, without yet assuming
q|X, because Y/q^2 is an integer. The carrier gives

    mu | k-R-1,

while the first Pell recurrence gives k=2n_first modulo 4XY^2.
The inequalities 1<=n_first<p=R<mu yield

    2n_first=R+1.

Therefore v=k-R-1 is a positive multiple of 4XY^2 and in particular of U.
The carrier divisibility now gives q|HX. Since gcd(q,H)=1, q|X.
Writing w=X/q, the restored source main gap is

    gamma_old=gamma+w-v/U.

It is integral, and g>(a+1)c together with c>X makes it positive, as in
the adaptive-carrier proof of source 72. All source requirements now hold.

### Completeness

Use the canonical source witnesses from source 69's completeness argument.
The same first carrier and resultant witnesses work. Their index difference
v is a positive multiple of 4XY^2, so v/U is an integer and

    v/U >= XY/q^2 = wY/q >= wq^2 > w.

Set gamma=gamma_old+v/U-w. It is positive and makes Dstar=Ug. The
canonical repunit still has J=1 modulo 6, so no new restriction is imposed
on any coefficient or canonical source dimension.

### Exact degree

The residual degrees are now 15,13,50; their product gives exact degree 78.
With q0=6beta j and the same k0,Bt0 notation, the carrier leading forms are

    (A0)15=-2q0^8 k0^2 X Y^2 Bt0,
    (A1)13=32q0^2 k0 X^2Y^4[4q0^2Y gamma+q0^3(q0-F)],
    N50=4(X^2Y^2)^4(k0Y)^8 t^8 q0^6(q0-F)^2 n^2.

Their product has nonzero coefficient 1024*(6beta)^18 at

    j^18 F^2 eta^11 X^12 Y^23 t^8 n^2 gamma alpha.

The exact evaluator has 103 gates (58 multiplications,26 additions,19
subtractions), one more than source 69's degree-82 evaluator. This is a
degree/operation tradeoff, not dominance in both quantities.

## 4. Verification boundary

The checkers perform exact sparse-polynomial identities, complete graph
well-formedness/liveness checks, selected-coefficient degree certificates,
byte-identical rebuilding, and authentication of the included fixed
numerals. The twelve-variable checker additionally verifies the exact
descent identity and finite local Pell examples. These computations support
the formulas and finite data. The universal proof is the argument above
composed with the named upstream arithmetic and native semantic theorems.

Run `python3 eleven/verify.py` and `python3 twelve/verify.py` from this folder.
Both also pass with `python3 -O`, which does not disable their explicit checks.

The construction does not prove Con(ZFC), find a contradiction, or decide
whether either equation has a solution. It proves the equivalences.
