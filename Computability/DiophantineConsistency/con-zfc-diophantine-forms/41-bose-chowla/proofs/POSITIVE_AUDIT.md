# Independent mathematical audit of the new twelve-positive separator

## Scope and conclusion

The strengthened separator

    M = k(ik^3+T)^2

is sufficient for the inherited three-root recovery argument, provided the
authentic weak compiler interface stated below is used. The carrier may be

    delta=(a+2)c-ell,
    sigma=b+M delta+v(a+2)I,
    L=1+HM,
    W=b0+H(t+sigma).

No factor4 and no half-correction are needed. This audits the mathematical
zero-set argument and, in Section6, independently checks the frozen
degree calculation. It does not independently reprove the inherited
compiler or rational-root recovery lemmas. Operation counts are outside
this note's mathematical audit.

## 1. Required source interface

All twelve supplied coordinates are positive. Use the coordinate shift
omega=w+q and the definitions

    X=q(w+q), Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=(a+2)^2-1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2,
    I=ic^2, D=1+Delta I^2, Q=(Delta I)^2, d=Q-1,
    v=cT, b=c+RD, b0=X+ac.

The inherited authentic weak interface, before deleted roots are
recovered, gives

    q>=16, Y>=q^3, 3q<R<q^4-2,
    E>R+2, k=R+epsilon+hE>E,
    kY<c<k(Y+1),
    sqrt(G)-sqrt(A)>kY^2,

where epsilon is either unit sign. The new w coordinate strengthens
X>=q to X>=q(q+1). The inequality sqrt(G)-sqrt(A)>kY^2 is an inherited
interface statement; it is not inferred from the new M or assumed after
the roots have already been reconstructed.

These imply a>R+2 and c>a. For the latter, c>kY>XY^2>Y(X+1)=a.

## 2. Sharp bound on the auxiliary roots

Let Z=v sqrt(D)+b. First b<d. Indeed

    d-b=Delta I^2(Delta-R)-(R+c+1).

Since Delta>R, I>=c^2 and R<c, the first positive term is at least c^4,
whereas R+c+1<=2c. As c>=2, c^4>2c. Thus d>b>D>sqrt(D).

For either f=+sqrt(D) or f=-sqrt(D), the auxiliary root satisfies

    d y^2 = Q(vf-b)^2-1.

This root can be complex, so an argument bounding only real y would be
insufficient. Taking absolute values and using Z>1 gives

    |y|^2 = |Q(vf-b)^2-1|/d < QZ^2/d.

Because Q=d+1 and sqrt(1+1/d)<1+1/d,

    |y|<Z+Z/d<Z+v+1.

This is the sharp bound used below. The weaker inherited bound |y|<2Z
does not by itself justify dropping the factor4 from M.

## 3. The new separator inequality

Put U=a+2. Then sqrt(D)<UI because D=U^2 I^2-I^2+1 and I>1.
The dominant b term satisfies

    R U^2 c^4/(k^8 Y^2)<1.

To verify it without assuming any recovered Pell root, use R<q^4,
c<k(Y+1), k>XY, X>=q(q+1), Y>=q^3. The left side is bounded above by

    [ q/(q+1) (1+q^(-2)+2q^(-5)) (1+q^(-3))^2 ]^2.

The bracket is less than1. For q>=4,

    (1+q^(-2)+2q^(-5))(1+q^(-3))^2
       <=(1+2/q^2)(1+3/q^3)
       =1+2/q^2+3/q^3+6/q^5
       <1+1/q.

The actual q>=16 is well within this range. Consequently

    R D/(kY^2)<i^2 k^7.

For the mixed term, the rough bounds U<2XY and c<2kY suffice:

    v sqrt(D)/(kY^2)
       < iT U c^3/(kY^2)
       <16iT Xk^2Y^2
       <(16/X)iTk^4
       <iTk^4.

The last inequality uses X>=q(q+1)>16. Also

    c/(kY^2)<1,
    v/(kY^2)<T,
    1/(kY^2)<1.

Combining these strict inequalities yields

    (Z+v+1)/(kY^2)<i^2k^7+iTk^4+T+2
                        <k(ik^3+T)^2=M.

The final comparison follows by expansion: the difference is
iTk^4+kT^2-T-2>0 for i,T>=1 and k>=2. Therefore

    |y|<M kY^2<M(sqrt(G)-sqrt(A)).

This is the separator required by the existing root argument.

## 4. All recovery hypotheses remain available

Every root x=+/-M sqrt(A)+y of the inner polynomial obeys

    |x|<M sqrt(G).

Also sqrt(A)>ell=XkY^2, so |y|<M kY^2<M sqrt(A); hence the inner
polynomial does not vanish at x=0. Moreover

    M sqrt(A)>X M kY^2>XZ>2Z.

Since 2Q/d<4 and Z^2>Dv^2+b^2, this implies

    d M^2 A>2Q(Dv^2+b^2).

This is the separate positivity/nonzero-denominator condition used by
the inherited explicit rational-recovery formulas. It is important to
check it in addition to the absolute root bound.

The norm identity still makes N congruent to a square modulo4. Thus a
zero of Nk Nt(1+N)-1 has N=0 and Nk=Nt=epsilon. At this point all the
weak bounds above apply. If G were nonsquare, conjugation would force
both (W-Lsqrt(G))/H and (W+Lsqrt(G))/H to be roots of the inner rational
polynomial. Their distance exceeds 2M sqrt(G), contradicting the root
bound. Hence the selected main root is integral. It is positive because
W>0; choosing its negative sign gives x>M sqrt(G).

The source rational formulas now recover f,tau and the auxiliary root y;
the inherited rational Pell saturation lemma makes y integral. Because
W=b0 modH and L=1 modH, the main Pell root is b0 modH, yielding the same
positive gamma and the same signed quotient compiler interface. This
finishes soundness with no use of a canonical-witness assumption.

## 5. Completeness and the translated positive coordinate

The correction sigma is positive. Indeed

    delta=Uc-ell=kY^2+2kY+U eta>0.

On a canonical positive source witness, let g=sqrt(G), tau=sqrt(A),
f=sqrt(D), and retain its positive auxiliary y and gamma. Since
ell/c>E/2>2,

    delta=(a+2)c-ell<ac<g.

Define

    t=gamma+M(g-delta)+M tau+y-b-vUI.

All terms are integers. Since UI<2sqrt(D),

    b+vUI<2Z<M tau,

so t>0. Its defining identity gives

    W=Lg+H(M tau+y),

and therefore N=0 with Nk=Nt=1. The inherited recovered power
X=omega q=2^R and R>3q ensure omega>q, so the additional coordinate
change w=omega-q is positive on canonical witnesses. Thus the w shift
also preserves completeness.

## 6. Independent check of the exact degree and leading form

For the final frozen construction, use the notation of the delivered
POSITIVE_PROOF.md. Let q0=beta J, k0=eta+zeta, omega0=w+q0,
Y0=sq0^3, E0=omega0 q0Y0, c0=k0Y0, and R0=q0^3(q0-F).
The leading forms of I,D,Q,b,sqrt(D),H,M are respectively

    i c0^2, E0^2 i^2 c0^4, E0^4 i^2 c0^4,
    R0 E0^2 i^2 c0^4, E0 i c0^2, 4E0, i^2k0^7.

The Laurent root expansions give g-tau=delta-k/2+O(lambda^-1)
and f0-f of degree5, with leader I0/(2E0), where f0=(a+2)I.
Thus the four corrected-linear quantities C_(sa,sg) in the proof have
degrees26,26,24,17, with leaders

    -8i^2 k0^7 E0^2 c0,
     8i^2 k0^7 E0^2 c0,
     8i^2 k0^8 E0 Y0^2,
     2i c0^3 T.

For each of the four positive-f factors, the unique leading term is
4H^2Qvb f, of degree119 and leader

    2^6 R0 E0^9 i^5 c0^11 T.

For each negative-f factor, the leading term is 2dHb C_(sa,sg).
The common multiplier has leader 2^3R0E0^7i^4c0^8, degree90.
The resulting degrees are116,116,114,107. The sum is
4*119+116+116+114+107=929.

Multiplying all eight leaders gives

    -2^46 R0^8 E0^69 i^43 c0^81 k0^22 Y0^2 T^5
    =-2^46 i^43 k0^103 T^5 s^152 omega0^69
       q0^549(q0-F)^8.

This is nonzero for every authentic beta>0. Multiplication by NkNt
adds7+2 degrees and cannot cancel it, because the added constant/product
terms have strictly smaller degree. Thus the final polynomial has exact
degree938. This check is symbolic and does not rely on the numerical
ray tests.

## Audit verdict

The separator and carrier modification are sound and complete relative
to the explicit inherited weak and rational-recovery interfaces. The
argument needs the shifted X=q(w+q), the sharp |y|<Z+v+1 bound, and the
separate rationality inequality; none may be omitted. No issue was found
with the final unscaled M=k(ik^3+T)^2 construction. The frozen
degree938 claim and its explicit nonzero leading form also pass the
independent symbolic check in Section6.
