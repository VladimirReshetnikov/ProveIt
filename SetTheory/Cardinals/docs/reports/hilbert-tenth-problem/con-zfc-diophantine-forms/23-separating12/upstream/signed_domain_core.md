# Six free signed ports and a 33-integer-variable consistency equation

Final combined instance: use the complete four-port T4 tuple in ../bridge/T4_CONSTANTS.json. Its full compiler contract and canonical rank R = 3 modulo 4 are proved in ../bridge/BRIDGE_AUDIT.md. Historical packet06/08 coefficient discussions below document the derivation or a separate fallback, not a license to mix numerical ports. The arithmetic and witness arguments are unchanged.

Source pin: ProveIt `3b201cdea32d2c816f5f3d20734051f25fd3ef14`.
This sign reduction keeps its selected complete coefficient tuple unchanged. The main T4 tuple and the separate historical 06-blank67 tuple both satisfy the required compiler contract. No individual ports or window orderings may be mixed.

## Result

In the inputless ordinary-strong hybrid, only the following nine original ports need be strictly positive:

    J, F, alpha, z, i, s, w, eta, zeta.

The remaining six ports may independently range over all integers:

    h, f, T, gamma, tau, y.

Here T is `auxiliary_quotient`, z is `transport_quotient`, tau is `tau_root`, and y is `y_aux`. The statements are existential equivalences, not claims that every signed solution becomes the original positive solution by taking coordinatewise absolute values.

Consequently substitute, for just those nine positive ports,

    x = 1 + u_x^2 + v_x^2 + r_x(r_x+1).

The six free signed ports remain unchanged. This yields 9*3+6=33 unrestricted integer variables. The system has six comparisons and an explicit 124-operation circuit; the single product equation has 132 operations and exact degree 190; the sum-of-squares equation has 141 operations and exact degree 100. These counts include all substitutions, with seven binary arithmetic operations per positive port. The unsigned core counts remain respectively 61, 69, and 78.

The positive parametrization is surjective by Legendre's three-square theorem applied to 4(x-1)+1. Thus it introduces no assumption about attainable positive values.

## Exact hybrid and notation

Use the shared definitions of packet 06:

    q=mJ+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    D=X+ac+gamma H,
    G=(q-1)(q-F)+alpha,
    R=G(q^2-1)+(MC+q MFsrc)J,
    V=c(Tf-1)-R f^2,
    I=ic^2, S=Delta(f^2-1).

Let A=a+2, P0=2XY^2+1, and define

    N0=tau^2-(EkY)(EkY+k),
    N1=D^2-Delta c^2,
    NA=S(V^2-y^2)+y^2,
    NK=k-hE-R,
    NT=(K+w)C+q-F-z(q-1),
    NS=1+I^2-S.

The single polynomial is N0*N1*NA*NK*NT*NS-1. The system is N0=N1=NA=NK=NT=1 and I^2=S.

## 1. Unit extraction does not use the six relaxed signs

At a product zero every factor is an integer unit. Delta is 0 or 3 modulo 4, so N1 cannot be -1. NS cannot be -1 either: if Delta=0 modulo 4 then NS=1+I^2 modulo 4; if Delta=3 modulo 4 then NS=I^2+f^2 modulo 4. Thus NS=1 and S=I^2. Consequently NA modulo 4 is either V^2 or y^2, so NA cannot be -1. The consecutive-product negative Pell obstruction excludes N0=-1 with tau signed just as with tau positive. Hence

    N0=N1=NA=NS=1,
    NK=epsilon, NT=nu, epsilon,nu in {+1,-1}, epsilon*nu=1.

The six-comparison system trivially supplies this conclusion with both signs +1.

## 2. Raw bounds are unchanged

Only J,F,alpha,z,w,s,eta,zeta positivity is needed for the raw transport and packing bounds. In particular, C<0 would make NT<-1. The exceptional C=0 possibility is kept, as in packet 06. Its source proof supplies

    q>=16, q(q^2-1)<R<q^4-q^3+q^2-1<q^4-2,
    E>=q^4>R+2, a>R+2,
    X>=q, Y>=q^3.

None of h,f,T,gamma,tau,y was used to obtain these facts.

## 3. h is automatically positive

NK=epsilon gives k=hE+R+epsilon. If h<=-1 then k<=R+1-E<0, contradicting k>0. Thus h>=0.

The first norm gives k=2 psi_P0(n), n>=1, with |tau|=chi_P0(n). If h=0 then k=R+epsilon>2. The index n=1 gives k=2, impossible. For n>=2, k>=2 psi_P0(2)=4P0>R+1, also impossible because P0=2XY^2+1>=2q^7+1 and R<q^4. Hence h>0.

## 4. Main classification uses |D|

N1=1 gives |D|=chi_A(p) and c=psi_A(p), p>=1. D cannot vanish. This classification does not require gamma>0.

The unchanged first-index argument, using P0>A, c>k, and P0=1 modulo E, gives

    p>n, n>=(R-1)/2>=24,
    c>A Delta^2, c>2p, c>2R.

In particular c>X: n>=2 implies k>=4P0>X, and c>k. These conclusions use c and the absolute main root only, not D's sign or gamma's sign.

## 5. The ordinary strong rank theorem applies to |f|

Since i,c>0 and I^2=Delta(f^2-1), f is nonzero and |f|>1. Apply the ordinary strong lemma to |f|, c, i. The independently established c>A Delta^2 verifies its size premise. It yields m1>0 such that

    |f|=chi_A(m1), p divides m1, c divides m1,
    I=Delta psi_A(m1), m1>=c>2p.

Also c^2 divides f^2-1, because

    f^2-1 = i c^2 psi_A(m1).

Thus |f|>2c (alternatively use f^2=1+i^2c^4/Delta and c>A Delta^2).

This use of the ordinary strong lemma is essential. The standalone equation I^2=Delta(f^2-1) does not imply integrality in the A-Pell sequence without the large-c hypothesis.

## 6. Signed auxiliary rank: neither f nor T must be positive

NA=1 is

    (I V)^2-(I^2-1)y^2=1.

Because I>1, y=0 would give I^2 V^2=1, impossible. V=0 is impossible as well. The definition of V gives V=-c modulo |f|. Since |f|>2c and c>2, V cannot be +1 or -1. Therefore |V|>1 and |y|>0.

Positive Pell classification applied to (I|V|,|y|) gives an index lambda>0. I divides chi_I(lambda), so lambda is odd. Write lambda=2r+1 and use the integer polynomial Q_r with chi_Z(2r+1)=Z Q_r(Z^2). Then

    |V|=Q_r(I^2),
    Q_r(1-A^2)=(-1)^r psi_A(2r+1),
    Q_r(0)=(-1)^r(2r+1).

Modulo |f|, I^2=Delta(f^2-1)=1-A^2. Since |V|=+V or -V and V=-c modulo |f|, squaring gives

    chi_A(2lambda)=chi_A(2p) modulo chi_A(m1).

The signed chi step-down lemma, with 0<2p<m1, yields lambda=+p or -p modulo m1, hence modulo c.

Independently I is divisible by c. Since c^2 divides f^2-1, V=-R modulo c. Thus |V|=+R or -R modulo c. Reducing Q_r(I^2) modulo c yields R=+p or -p modulo c. The strict bounds 0<R,p<c/2 force p=R.

This proof deliberately does not reconstruct positive auxiliary variables o_old,j_old. Their positivity is unnecessary for signed rank; the needed congruences hold directly.

## 7. Exact first index and ratio estimates remain valid

With p=R, the source wrap-elimination argument gives 2n=R+epsilon. If epsilon=-1, the Pell duplication estimate contradicts kY<c<k(Y+1). Consequently epsilon=nu=1 and 2n=R+1. The source transport argument then excludes C=0.

Set r0=(R-1)/2>=1. An elementary lower-ratio argument makes independence from D's sign explicit. The standard recurrence bounds psi_A(n)>=(2A-1)^(n-1) and psi_P0(n)<=(2P0)^(n-1) give

    c/psi_P0(r0+1) >= [(2A-1)^2/(2P0)]^r0
                        > [(X+1)^2/X]^r0 > X^r0.

The strict middle inequality reduces to 12XY(X+1)+9X>2(X+1)^2, valid for X,Y>=1. Since c/psi_P0(r0+1)=2c/k<2Y+2 and X^r0>6, this gives Y>(X^r0-2)/2>X^r0/3. Thus, without either D's sign or gamma's sign,


    Y>X^r0/3, a>X^(r0+1)/3, 2^R<a, X<a.

## 8. A negative main root is impossible, recovering gamma's sign

In the ring modulo H=4a+3, Delta=a^2 and A=a+2. Substituting sqrt(Delta)=a in the Pell identity gives

    chi_A(R)-a psi_A(R)=2^R modulo H,
    chi_A(R)+a psi_A(R)=(2a+2)^R=2^(-R) modulo H,

because H is odd and 2(2a+2)=H+1.

If D<0, D=-chi_A(R), c=psi_A(R), and D-ac=X modulo H would give X=-2^(-R) modulo H, so H divides X*2^R+1. Yet

    H>4XY>(4/3)X^(r0+1)>X*2^R+1>0.

For the second strict comparison use X>=16 and r0>=1: the ratio of (4/3)X^(r0+1) to X*2^R=2X4^r0 is (2/3)(X/4)^r0>=8/3, leaving a gap greater than 1. This contradiction proves D>0.

Now the first congruence gives X=2^R, since both lie between 0 and a<H. Moreover chi_A(R)>(a+1)c, since Delta>(a+1)^2. As c>X,

    gamma H=chi_A(R)-ac-X>c-X>0.

Thus gamma is automatically positive.

## 9. Finish and converse

Power extraction, inverse population packing, native decoding, and the K215 halting/finite-refutation endpoint now apply exactly as in packet 06. No remaining downstream step uses the signs of f,T,tau,y; those quantities have already served their only role in rank recovery. Thus every mixed-domain solution implies K215 halts. Conversely every positive solution furnished by the original completeness proof is a mixed-domain solution; the ordinary strong port is obtained as usual by i_new=Delta*i_old. This proves the existential equivalence in both directions, and hence the equivalence of nonexistence with Con(ZFC).

## Uniform degree certificate

Give the nine positive ports weight 2 and the six free signed ports weight 1, corresponding to the parametrization. Put Q=mJ, k0=eta+zeta, and T0=w(Q-F-alpha)-zQ. The leading forms of the six product factors are

    -w^2 s^4 Q^14 k0^2,
    8 gamma w^2 s^3 Q^11 k0,
    w^2 s^4 Q^14 k0^2 T^2 f^4,
    -h w s Q^4,
    T0,
    i^2 k0^4 s^4 Q^12.

Their weighted degrees are 44,35,50,13,4,44. The product leading form is

    8 Q^55 h gamma i^2 k0^9 w^7 s^16 T^2 f^4 T0,

of weighted degree 190. Its term using -zQ and eta^9 has coefficient -8m^56, nonzero since m>0. Replacing each positive port by its disjoint quadratic parametrization preserves this leading form nontrivially: set v_x=r_x=0 to obtain the injective monomial map x->u_x^2. Thus the signed product degree is exactly 190, not merely bounded by 198.

The auxiliary residual is the unique highest-weight residual (weight 50), so its square gives exact sum-of-squares degree 100 with no cancellation over the integers. The system's maximum degree is exactly 50 after substitution.

For the same domain relaxation in the older normalized product, the factor weights are 44,35,116,13,4,92, giving degree 304. The reduced-auxiliary normalized product has factor weights 44,35,50,13,4,92 and degree 238. These are valid but inferior to the ordinary-strong hybrid on degree.

## Verification boundary

This is an ordinary mathematical reduction using pinned source lemmas, not a newly kernel-checked theorem. Finite arithmetic diagnostics do not prove the number-theoretic rank, half-binomial, native compiler, or logical endpoint lemmas. No huge coefficients or accepting witnesses are evaluated. No assertion of Con(ZFC) or of global minimality is made.
