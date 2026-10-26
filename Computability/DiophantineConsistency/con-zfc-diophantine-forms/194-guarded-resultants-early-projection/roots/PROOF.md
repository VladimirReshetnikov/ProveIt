# Guarded quadratic trace elimination: thirteen unrestricted integers

## Result and boundary

Two fixed ordinary polynomials have thirteen unrestricted integer unknowns,
with exact degree / live binary-operation pairs **118/114** and **120/112**.
Every scalar multiplication and square is charged. The retained six fixed
coefficient integers and finite recipe are unchanged. The degree118 point
strictly dominates both inherited13/152/119 and13/156/117; the degree120
point is a further degree/cost tradeoff. These are not global minimality
claims, consistency assertions, or new kernel certificates.

The new step eliminates the signed strong-Pell trace from the unsquared
auxiliary row by a quadratic resultant. A strict guard supplies the nonzero
coefficient required to extract that trace. It is not legitimate to use a
resultant without proving this nonvanishing: its degenerate branch would
otherwise retain zeros with no rational trace. Both directions below apply
to every signed integer zero. Composing the retained even-strong and
native/compiler/refutation proofs establishes, in ordinary ZFC, that absence
of integer zeros is equivalent to syntactic Con(ZFC).

## 1. Entire literal polynomial

In both charts the ordered inputs are

    j,C,z,h,r,v,w,T,c,n,y,p2,p3 in Z.

The six fixed ports are beta,K0,MC,MF,cone_A,cone_B, exactly as bound in
`inherited_round22/inherited_round20/inherited/coefficients/BINDING.json`.
MF is already shifted. In particular beta=2^1064921-1,
cone_A=2^1113 and cone_B=2^666104. Define

    J=6j+1, qm=beta J, q=qm+1, W=12w+4, X=qW, Y=v,
    F=(K0+W)C-z qm,
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    ell=XY^2, eta=c-Yk, L=ell k,
    I=(8r+4)c^2, Ds=Delta I^2, Fs=Ds+1,
    Q=Delta Ds, delta=Q-1, b=cT-R,
    dy=delta y, t=c+dy, tt=t^2, Lb=Fs b^2,
    Ares=Lb+tt-Q dy y-1,
    Hres=Ares^2-4Lb tt,
    q3=q^3, M=2q3, U=MH, Klo=X(2X-3c)-2,
    Z0=Un+M Klo+H(Y-q3),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2.

Choose the chart:

| exact degree | k | budget | Z |
|---|---|---|---|
| 118 | R+1+h ell | (Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(kq^2)^2] | Z0+UL |
| 120 | R+1+h E | (Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(kq3)^2] | Z0 |

The120-chart evaluator computes L=E(Yk), without separately computing ell.
Finish with

    G=budget-[1+p2^2+p3(p3+1)],
    Dt=1+L(L+k), U2=U^2, ga=U2 G, db=U2 Dt,
    N=(Z^2-ga-db)^2-4ga db,
    P=N Hres+N+Hres.                                      (1.1)

The final schedule saves one operation relative to the identical expression
P=(N+1)(Hres+1)-1. All names are polynomial abbreviations, not quantified
unknowns. There is no division, variable exponent, missing numeral, hidden
positivity convention or consistency search in either DAG.

## 2. Algebraic resultant and why its exceptional branch matters

For an additional proof-only integer f, set V=fb-c and

    Ea=V^2-(Q-1)y(2V+y).

The complete identities, without assumptions, are

    Ares=Fs b^2+c^2-1-delta y(y-2c),
    Ea-1=Ares-2bt f+b^2(f^2-Fs),
    Hres=Ares^2-Fs(2bt)^2.                              (2.1)

Thus every pair of equations f^2=Fs and Ea=1 implies Hres=0. Conversely,
Hres=0 supplies f=Ares/(2bt) only if bt!=0. Without that fact the resultant
has an exceptional branch Ares=bt=0; mere elimination does not rule it out.
Section4 rules it out on every zero of the actual final polynomial.

## 3. Unit extraction and guard restoration

Unconditionally q is even and nonzero: beta>1 is odd and beta(6j+1) cannot
be -1. Thus |q|>=2, |W|>=4 and |X|>=8. Since a=(X+1)Y, either a=0 or
|a|>=7, and Delta=(a+2)^2-1>=3. H is odd and nonzero, so U!=0. Also
ell=XY^2 is even and ell(ell+1)>=0, hence Dt=1+ell(ell+1)k^2>=1.

Both N and Hres are squares modulo4. At P=0 the integers N+1 and Hres+1
are units; neither can be -1, since that would make the corresponding
square residue equal2 modulo4. Therefore N=Hres=0. Conversely those two
equalities imply P=0.

Put rho=Z/U in Q. Dividing N=0 by U^4 gives

    (rho^2-G-Dt)^2=4G Dt.                              (3.1)

Since Dt>=1, G<0 is impossible. Thus G>=0 and budget>0, which implies
Yk!=0. Also budget<=q^2Y^2k^2 and |ell|>=8, so

    Dt>=1+ell^2 k^2/2
      >=1+8q^2Y^4k^2>q^2Y^2k^2>=budget>G.             (3.2)

If rho=0, (3.1) would give Dt=G, contradicting (3.2). Hence define

    p=(rho^2+G-Dt)/(2rho), tau=rho-p.

Equation(3.1) yields p^2=G and tau^2=Dt. A rational number whose square
is integral is integral, by reducing its fraction to lowest terms. Thus
p,tau are integers, including G=0 and either sign of either root. This
covers coincident square classes and all signed roots without a genericity
assumption or a division by a possibly zero rho.

Write s=1 for the118 chart and s=0 for the120 chart. Set

    p1_old=p, n_old=n+sL-(2L+k)-p+tau.                  (3.3)

All restored coordinates are integers. The old carrier numerator is
Zold=U n_old+M Klo+H(Y-q3). The identity

    (Zold+Uk)^2+4U(L Zold-U)
       =(Zold+U(2L+k))^2-4U^2 Dt

shows its carrier residual vanishes because
Zold/U+2L+k=rho-p+tau=2tau. The old guard residual is
budget-1-p1_old^2-p2^2-p3(p3+1)=0.

## 4. Unconditional-on-zeros trace recovery: every denominator is nonzero

The following consequences use only the restored carrier and positive budget,
not a strong trace, auxiliary witness or Pell-index classification. The
retained centered-disk and authentic-mask argument gives

    q0=|q|>=16,  q0(q0^2-1)<R<q0^4-2,
    |c|>|k|(|Y|-1/2),
    |Y|>q0^2 and |ell|>3R+1               (118 chart),
    |Y|>q0^3 and |E|>3R+1                (120 chart).

Precisely, write B0=k^2(q^2-Derr)-4q^2 eta^2. In the118 chart,
budget=Y^2 B0-k^2q^6>0 gives B0>0 and |Y|>q0^2. The120 chart
similarly uses q^8 and gives |Y|>q0^3. B0>0 gives the centered disk
Derr<q^2 and |eta/k|<1/2. The authentic mask lemma then bounds R as
above independently of the strong and auxiliary equations. Finally
|ell|=|X|Y^2>4q0^5>3R+1 in the118 chart, while
|E|=|X||Y|>4q0^4>3R+1 in the120 chart. These are exactly the early
arguments retained in inherited_round22/PROOF.md Section3 and its cited
source153 Section2 and q8 signed source. There is no circular application
of their later Pell classification.

Let d=ell or E according to chart. Since k=R+1+hd, R>0 and |d|>3R+1,
either h=0 and |k|=R+1, or

    |k|>=|d|-(R+1)>2R>=R+1.

Consequently |c|>|k|(|Y|-1/2)>R>0. For every integer T this proves
b=cT-R!=0: T=0 gives b=-R, and T!=0 gives |cT|>=|c|>R.

Since c!=0 and |8r+4|>=4, one has |I|>=4c^2. Thus

    delta=Delta^2 I^2-1>=144c^4-1>|c|>0.

For every integer y, t=c+delta y is nonzero: y=0 gives t=c!=0;
y!=0 gives |delta y|>=delta>|c|. Therefore 2bt!=0. The equation
Hres=0 now gives the rational f=Ares/(2bt) satisfying f^2=Fs. Since
Fs is an integer, f is an integer. Identity(2.1) gives Ea=1, and
f^2-Delta I^2=1 is immediate. This handles arbitrary signs of c,k,Y,f,
b,t and arbitrary r, rather than selecting positive canonical witnesses.
The cases c=0, b=0 and t=0 are excluded by prior guards, not divided away.

Together with(3.3), every new zero has been restored to a literal zero of
the retained even-strong fifteen-integer kernel in
`inherited_round22/PROOF.md`, equations(2.5). Its complete signed proof,
Sections3–4, reconstructs fresh odd-scale f,T,r,y witnesses before applying
the authenticated native/compiler/refutation theorem. We inherit that
fresh-witness construction; we do not improperly reuse the new even-scale
trace in an odd-scale source theorem.

## 5. Reverse map on every old zero and completeness

Conversely, let any zero of that even-strong fifteen-integer kernel be given.
Its strong equation gives f^2=Fs, and its auxiliary equation gives Ea=1.
Hence (2.1) gives Hres=0 without requiring any division. The first carrier
equation gives (Zold/U+2L+k)^2=4Dt. A rational with integral square is an
integer, and an integer whose square is divisible by4 is even. Thus
Zold/U+2L+k=2tau for an integer tau. Set

    n=n_old-sL+(2L+k)+p1_old-tau.                       (5.1)

Retain all other thirteen coordinates and delete f and p1_old. Then
rho=p1_old+tau, G=p1_old^2 and Dt=tau^2. Direct substitution into(3.1)
gives N=0, and therefore P=0. No root sign is fixed. Equations(3.3) and
(5.1) are maps on all zero sets, although no assertion that they are inverse
polynomial automorphisms is needed or made.

The retained source constructs an even-strong kernel zero from every old
odd-scale zero by fresh doubled strong and auxiliary witnesses, and its old
source constructs a zero from every finite syntactic ZFC refutation. This
supplies canonical completeness without adding a Diophantine interpolation
hypothesis or presupposing consistency. Negating the two-way existence
equivalence gives the stated Con(ZFC) equivalence in ordinary ZFC.

## 6. Exact degrees at the authentic fixed numeral slice

Write homogeneous leading forms

    q0=6 beta j, X0=12q0 w, Y0=v, a0=X0Y0,
    F0=12wC-q0z, R0=-q0^3F0, ell0=X0Y0^2,
    U0=8q0^3a0, I0=8r c^2.

The resultant identities are expanded before degrees are assigned. In
particular Ares has degree22, not the spurious degree38 obtained by ignoring
the cancellation tt-Q dy y. Put

    D0=a0^2 I0^2, Q0=a0^4 I0^2.

Then [Fs]_12=D0, [delta]_18=Q0, [b]_5=-R0 and [t]_19=Q0 y.
The square Ares^2 has degree44, whereas 4Fs b^2t^2 has degree60, giving

    [Hres]_60=-4 D0 R0^2 Q0^2 y^2
             =-2^20 a0^10 r^6 c^12 R0^2 y^2.          (6.1)

For degree120, k0=R0, [G]_18=-R0^2q0^8,
[Dt]_18=ell0^2R0^2, and the unshifted Z has degree7. Hence

    [N]_60=U0^4R0^4(q0^8+ell0^2)^2.                  (6.2)

For degree118, k0=R0+h ell0 (the h term is retained), and set

    T0=cone_A^2 Y0^2F0^2+4q0^2Y0^4+q0^6.

Then [G]_16=-k0^2T0. The exact carrier cancellation

    (Z0+UL)^2-U^2Dt=Z0^2+2ULZ0-U^2(1+Lk)

has degree26. Consequently the complete degree58 norm top is

    [N]_58=4U0^4ell0^2k0^4T0.                         (6.3)

The complete output top is the product of(6.1) with(6.2) or(6.3);
the final +N+Hres terms are strictly lower degree. The accompanying
independent sparse checker expands every coefficient of these leading
forms and supplies explicit nonzero coefficients on the actual fixed
six-port slice. The explicit attained coefficients are

    [j^58 w^16 v^18 z^6 r^6 c^12 y^2] P118
        =-2^124 3^74 beta^58 !=0,
    [j^66 w^14 v^14 z^6 r^6 c^12 y^2] P120
        =-2^126 3^80 beta^66 !=0.

Their exponent sums are118 and120. To isolate them, set C=h=0 and select
the pure q0 power in T0 or (q0^8+ell0^2)^2; every alternative has a
different w,v exponent. The full output top has85 and21 monomials,
respectively. No generic-port degree estimate or sampled ray substitutes
for the complete leading-form calculation.

## 7. Reproducibility and inherited logical closure

`build.py --check`, `check.py`, `python -O check.py`, and
`reconstruct_coefficients.py` require only Python's standard library. They
reproduce every DAG, bind all live gates to separately written formulas,
prove the universal identities and full leading forms, check all six
complete fixed numerals and inherited pins, and reject each separately
mutated live binary gate. Optional external algebra-system diagnostics, if
present, are not part of required replay.

`inherited_round22/` retains the signed even-trace proof, prior exact
circuits and all its earlier native/coefficient/source closure unchanged.
The exact closure map distinguishes ordinary unbounded mathematical
arguments from finite transcription checks. No remote repository state is
changed and no new end-to-end proof-assistant certificate is claimed.
