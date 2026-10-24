# Independent review: normalized four-root projection to fourteen integers

## Review scope and conclusion

The normalization, signed soundness, four-root recovery, integral-coordinate
restoration, and compatibility with the canonical source-34 witnesses pass
this review. The reasoning below is independent of the proposed finite test
receipts. It uses the existing source-34 canonical arithmetic interface and
the previously proved positive auxiliary reconstruction lemma as identified
dependencies. It does not independently reprove the unbounded tile/compiler/
machine/refutation calibration.

The reviewed implementation is `new_integer_compression/build.py`, together
with its `four_root_integer14.json` output. I read the polynomial definitions,
both quadratic norm routines and their composition. Their algebraic formulas
agree with the mathematical projection described below. This note does not
certify the exact degree or the optimality of the operation count.

## 1. Literal normalization

Use the authentic port beta=2^1064921-1, which is odd and is 1 modulo 3.
Keep the existing fixed K0, MC, MF, cone_A and cone_B. Define

    J=6J6+1, q=beta J+1, W=4(3w3+1), X=qW,
    Y=(2v_scale+1)q^3, E=XY, a=(X+1)Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk, u=EYk,
    A=u(u+k)+1,
    L=(2r+1)c^2, F2=1+Delta L^2, Q=Delta^2 L^2,
    delta=Q-1, V=F2(cT-R)-c,
    D0=X+ac, Dm=1+Delta c^2.

The symbol A in this note is the first square radicand. To avoid confusion,
the Pell-sequence base a+2 is denoted A_star below.

The retained joint guard is the predecessor's exact polynomial

    det=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Tsign=eta(k-eta),
    Pos=1+p1^2+p2^2+p3(p3+1),
    G=det*Tsign-(pair_root^2-det-Tsign+1)^2-Pos.

All fourteen surviving coordinates are unrestricted integers. Every name
above is an ordinary polynomial abbreviation.

## 2. Guard consequences and nonzero denominators

The existing joint-sign proof is directly applicable: G=0 makes det and
Tsign strictly positive. The inequality Tsign>0 implies k is nonzero and
|eta|<|k|. Thus

    |c|=|Yk+eta| > (|Y|-1)|k|.

J=6J6+1 is a nonzero odd integer, so |q|>=beta-1>1. The odd scale 2v_scale+1
is nonzero; hence |Y|>=|q|^3. Consequently |c|>1 and L=(2r+1)c^2 is nonzero.
Since J and beta are odd, q is even, Y and a are even, and Delta is odd.
In particular Delta is nonzero, whence Q=Delta^2 L^2>1 and delta>0.
Also H=4a+3 is odd and cannot vanish. These conclusions use no deleted
strong equation and no recovered radical.

Writing b=XY^2 gives u=bk and

    A=b(b+1)k^2+1>=1.

This last fact is unconditional for integer b and k.

## 3. Four distinct 3-adic valuations

The authentic beta is 1 modulo 3, and J and W are 1 modulo 3. Therefore
q and X are 2 modulo 3, and a=(X+1)Y is 0 modulo 3. Thus Delta is 0
modulo 3 and H is a nonzero multiple of 3. Since b=XY^2 is 0 or 2 modulo
3, A=b(b+1)k^2+1 is 1 modulo 3. Finally

    F2=1+Delta L^2=1 modulo 3,
    Q=Delta^2 L^2=0 modulo 9,
    Dm=1+Delta c^2=1 modulo 3.

The rational number B=(QV^2-1)/(Q-1) is a 3-adic unit, because its
numerator and denominator are both -1 modulo 9. In any extension of
the 3-adic valuation, the four terms

    18 sqrt(F2), 6 sqrt(A), 2 sqrt(B), 2 sqrt(Dm)/H

have respective valuations

    2, 1, 0, -v_3(H).

They are pairwise distinct. All radicands are nonzero. The valuation
separation lemma in `VALUATION_SEPARATION_REVIEW.md` therefore proves:
if any signed sum of these terms is rational, each square root is rational.
No assumption that B is positive is needed before applying the lemma.

## 4. The composed norm produces exactly the required signed sum

The first degree-four polynomial in a carrier x is the cleared norm for
the two roots 3*tau and y, with tau^2=A and y^2=B. Equivalently its
zero condition is a signed equality

    x+3(2u+k)+2V = +/-6 sqrt(A) +/-2 sqrt(B).

Its explicit cancellation-exposed coefficients agree with the previously
reviewed 16-variable norm.

Put M0=D0^2-Dm. Expanding gives the implementation's expression

    M0=X^2+2Xac-Hc^2-1.

The proof-only variable w=H*gamma satisfies

    w^2=-2D0*w-M0.

Taking the quadratic norm of H^4*N16(x-2w/H) therefore adds the root
2*gamma=2*(d-D0)/H, where d^2=Dm. H is nonzero, so the clearing factor
does not add a zero branch.

Next put fc=(a+2)L. The proof-only centered strong root z=f-fc satisfies

    z^2=-2fc*z+(1-L^2),

because fc^2-F2=L^2-1. Taking the quadratic norm of the preceding
degree-eight polynomial at x-18z adds 18(f-fc). Therefore a zero of
the resulting N14 gives a signed-root identity whose rational side is

    xi+3(2u+k)+2V+18fc+2D0/H

and whose other side is a signed sum of the four terms in section 3.

Conversely, integral roots tau,y,d,f with gamma=(d-D0)/H integral give
an integral carrier

    xi=6tau+2y+2gamma+18(f-fc)-3(2u+k)-2V,

for which the two successive norms vanish.

The builder's pair arithmetic uses the identity

    Norm(e+ow)=e^2+trace*e*o-constant*o^2

for w^2=trace*w+constant. Its denominator-cleared polynomial routine
computes denominator^n*f(x-scale*w/denominator), exactly as required.
These algebraic identities hold even when the quadratic splits over Q.

## 5. Integral recovery and restoration of every deleted coordinate

At G=N14=0, section 3 gives rational f,tau,y,d. Since F2,A,Dm are
integers, monicity of the three square equations makes f,tau,d integral.
The adjacent-coefficient descent makes y integral from

    QV^2-(Q-1)y^2=1, Q>1, V integer.

The carrier gives 2*gamma integral, while H*gamma=d-D0 is integral.
H is odd, so gamma is integral. This parity argument is essential; no
parity of xi should be assumed before it.

Define the ordinary strong multiplier and its coordinate by

    i_old=Delta(2r+1), r_old=(i_old-1)/2.

Delta and 2r+1 are odd, so r_old is integral. The ordinary strong square
is I_old=i_old*c^2=Delta L and I_old^2=Q. The recovered f satisfies
f^2=F2=1+Delta L^2, giving exactly

    I_old^2-Delta(f^2-1)=0.

Restore the CRT coordinates polynomially by

    o=f(cT-R),
    j_old=F2*T-1-Delta(2r+1)^2 c^3 R.

Then fo-c=F2(cT-R)-c=V, and

    c*j_old-V-R=0,
    1-V+c*j_old+hE=R+1+hE=k.

The second identity uses f^2-1=Delta(2r+1)^2c^4, so there is no division
or unproved strong-rank prerequisite. All deleted rows of the original
integer interface are restored. Also J3=2J6 restores its old J variable.

This is a material advantage over the unnormalized 15-variable route:
the CRT restoration no longer depends on a preliminary c|f^2-1 theorem.

## 6. Canonical completeness and source-34 parity compatibility

The exact source is the existing source34 coefficient proof, section
`Canonical parity promises and signed-family transfer`, at

    incoming_full_audit/con-zfc-radical-guard-descent-2026-10-23/
    con-zfc-cross-guard-descent-2026-10-23/integer/upstream/
    source34_COEFFICIENT_PROOF.md

It explicitly establishes the following canonical properties, including
their preservation under rank tuning:

* B=2^1064921, q=B^N=2^t with N and t odd;
* R=3 modulo 4 and R>t;
* W=X/q=2^(R-t) is a positive square;
* A_star=a+2 is even;
* c=psi_A_star(R) is odd;
* m=cR gives psi_A_star(m)/c^2 positive and odd;
* Y/q^3 is positive and odd.

Since beta=B-1, J=(q-1)/(B-1)=1+B+...+B^(N-1). It is odd, and for
odd N the alternating sum modulo 3 is 1. Thus J=1 modulo 6, exactly
the new normalization. Because R-t is positive and even, W/4 is a
positive power of 4 (including 1), so W/4=1 modulo 3, exactly the
existing w3 normalization. The odd Y/q^3 gives the v_scale coordinate.

For clarity, the strong choice can also be checked directly. Let

    m=cR, L=psi_A_star(m), f=chi_A_star(m).

The composition formula gives L=c*psi_d(c), with d=chi_A_star(R) and
d^2-1=Delta*c^2. The Pell binomial expansion modulo c shows
psi_d(c)=c*d^(c-1)=0 modulo c, hence c^2 divides L. Since A_star is
even and m is odd, psi_A_star(m) is odd; c is odd, so L/c^2 is odd.
It follows that r=(L/c^2-1)/2 is an integer, and f^2-Delta L^2=1.

The required auxiliary witnesses follow from the existing positive
auxiliary reconstruction lemma in

    incoming_full_audit/ZFC_Diophantine_Joint_Guards_2026-10-24/
    ZFC_Diophantine_Joint_Guards/pell/upstream/package61_report.tex

at lines 493--533 of the inspected version. Its hypotheses are exactly
R>=3, R=3 modulo 4, c=psi_A_star(R), f,L>0,
f^2-Delta L^2=1, and c|L. It supplies positive T,y with

    V=f^2(cT-R)-c, QV^2-(Q-1)y^2=1, Q=(Delta L)^2.

Thus the stronger square-modulus T expression is genuinely available for
the newly chosen strong index m=cR. It is not inferred by dividing an
arbitrary previous auxiliary coordinate by f. Changing these strong and
auxiliary witnesses leaves q,X,Y,a,c,R,k,eta and the determinant guard
unchanged, so the inherited ordinary/main roots and positivity witnesses
remain applicable. The integral carrier from section 4 completes the lift.

## 7. The product finalizer is exact on all integers

The final polynomial is P=N14+G^2+N14*G^2. Its integer zero condition is

    (N14+1)(G^2+1)=1.

Since G^2+1 is a positive integer, it must equal 1. Hence G=N14=0.
The converse is immediate. No claim that N14 is nonnegative is required.

## 8. Remaining qualification

The new arithmetic proof above supplies the projection/restoration and
canonical completeness relative to the identified existing source and
calibration theorems. A final claim of exact degree 700, exact gate count,
or byte-identical coefficient binding requires its separate implementation
and degree certificate. This review does not elevate inherited numerical
checks into an end-to-end formal ZFC proof certificate, and makes no global
minimality or historical novelty assertion.
