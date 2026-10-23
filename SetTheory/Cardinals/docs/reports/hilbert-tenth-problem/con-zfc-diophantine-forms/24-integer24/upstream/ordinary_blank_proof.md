# Ordinary strong norms and signed witnesses for the blank computation

This note combines the blank-input compiler of package 06 with the ordinary
strong-norm argument of package 02. It adds a transport-coordinate shift and
two signed-root lemmas. All source references are pinned to ProveIt commit
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

The result is a 15-positive-variable, six-equation system with 60 binary
arithmetic operations and maximum degree 28; its sum of squares has 77
operations and degree 56. A related product equation has 69 operations and
degree 99. A stronger domain theorem permits six coordinates to be arbitrary
integers, giving explicit 33-integer-variable equations of degrees 190 and
100 with 132 and 140 operations respectively.

These are arithmetic refinements of a compiler theorem, not a formal Lean or
Rocq verification. The fixed numerals must be the authentic blank K215
compiler coefficients, or coefficients from another compiler whose same
interface has been proved. Arbitrary choices of the four numeral ports have
no computation or consistency interpretation.

## 1. Equations and coefficient interface

Write the strictly positive source coordinates as

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

The constants are beta=B-1, K, MC, MFsrc. Here B=2^d, d>=4,
K=DC+B*DR, MFsrc=MF+B-1, and the native masks satisfy

    0<MC,MF<B-1, MC=2 mod4, MF=4 mod8,
    popcount(MC)+popcount(MF)=d.

The blank compiler supplies the native-window semantics and canonical
completeness with positive alpha. Define

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, A=a+2,
    H=4a+3, Delta=A^2-1=a^2+H, D=X+ac+gamma H,
    G=(q-1)(q-F)+alpha=q(q-F)-C,
    R=G(q^2-1)+(MC+q MFsrc)J,
    L=E kY, V=c(Tf-1)-Rf^2, I=ic^2,
    A0=Delta(f^2-1).

The six equations are

    tau^2-L(L+k)=1,
    D^2-Delta c^2=1,
    A0(V^2-y^2)+y^2=1,
    k-hE-R=1,
    (K+w)C=F+z(q-1),
    I^2=A0.                                      (S)

The source `ordinary_blank_system60.json` computes both sides with exactly
34 multiplications and 26 additions/subtractions. Equality tests are not
arithmetic gates. The six residual degrees are 22,18,28,7,2,22.

For the product version retain instead the old positive transport coordinate
z_old and put

    N0=tau^2-L(L+k), N1=D^2-Delta c^2,
    Na=A0(V^2-y^2)+y^2, Nk=k-hE-R,
    Nt=(K+w)C+(q-F)-z_old(q-1), Ns=1+I^2-A0.

Then the polynomial is

    P69=N0 N1 Na Nk Nt Ns-1.                      (P)

It uses 39 multiplications and 30 additions/subtractions. Its exact factor
degrees are 22,18,28,7,2,22, summing to 99.

## 2. The expanded signed domain

The complete soundness argument below remains valid with just these nine
coordinates strictly positive:

    J,F,alpha,z,i,s,w,eta,zeta.

The six remaining coordinates

    h,f,T,tau,y,gamma

may range over all integers. In the product equation z means z_old; in the
system it means the shifted transport coordinate. At every zero h and gamma
are automatically positive. The other four signed coordinates need not be
made positive on the same tuple. Existence equivalence with the original
positive compiler is supplied by canonical completeness.

## 3. Unit signs and outer bounds

At a zero of (P), all six factors are integer units. Delta is 0 or 3 modulo
4, and A0=Delta(f^2-1) is 0 or 1 modulo 4. Consequently N1, Na, and Ns cannot
equal -1: N1 is a difference of a square and 0 or three times a square; Na
reduces to y^2 or V^2; Ns=1+I^2-A0 has residue 0,1 or 2. Thus all three
equal +1 and I^2=A0>0. In particular |f|>=2 and A0=I^2>1.

For the first norm put b0=XY^2>1. Its negative equation would be
tau^2-b0(b0+1)k^2=-1. This has no positive k. An elementary descent is as
follows. If x^2-n(n+1)t^2=-1 with n>=2 and t>0, then

    nt < |x| < (n+1/2)t.

The integer t'=(2n+1)t-2|x| consequently lies strictly between 0 and t.
Multiplication by the norm-one unit 2n+1-2 sqrt(n(n+1)) gives another
integer solution of norm -1 with second coordinate t', contradicting
minimality. Hence N0=1. Write Nk=epsilon and Nt=nu, each in {+1,-1}; their
product is +1.

The system (S) directly gives C>0 because its transport right side is
positive. For the product, the identity

    (q-F)-z_old(q-1)=1-F-(z_old-1)(q-1)<=0

and K+w>=2 show that Nt in {+1,-1} forces C>=0. Do not discard the C=0
boundary until the unit signs are recovered.

In either case q-F=C+alpha>0. Consequently

    q <= G=q alpha+(q-1)C <= q^2-q.

The valid mask bounds give

    0<(MC+q MFsrc)J<(q-1)(1+2q),
    q(q^2-1)<R<q^4-q^3+q^2-1<q^4-2,
    R-2>3q+1, E>=q^4>R+2, a>R+2.                 (1)

These are precisely the weakened blank-input bounds; the unavailable
stronger bound R<q^4-q^3 is not used.

## 4. Bootstrap and ordinary strong-rank recovery

Write chi_A and psi_A for the ordinary Pell sequences. The first norm has
fundamental positive unit 2XY^2+1+2 sqrt(XY^2(XY^2+1)), since a solution
with second coordinate 1 is excluded by the interval between consecutive
squares, and second coordinate 2 is attained. Thus, with P0=2XY^2+1,

    |tau|=chi_P0(n), k=2 psi_P0(n), n>=1.

The main norm gives |D|=chi_A(p), c=psi_A(p), p>=1. It does not require
gamma or D to be positive. Since P0>A and c>k, one has p>n. Also P0=1
modulo E, so

    2n=R+epsilon modulo E,
    2n=R+epsilon+vE, v>=0,
    n>=(R-1)/2>=24.                                (2)

Here epsilon=1 for (S). The nonnegative integer v follows solely from
2n>0 and 0<R+epsilon<E, not from any sign of h. It follows that

    c>A Delta^2, c>2p, c>2R.                        (3)

For the last bound one can simply use p>=25 and c>=psi_A(2)=2A>2R;
no positivity of h has been assumed.

Apply the ordinary strong-rank lemma to

    (ic^2)^2=Delta(f^2-1), c=psi_A(p)>A Delta^2.

It yields

    |f|=chi_A(m), p|m, c|m, m>=c>2p,
    I=Delta psi_A(m).                              (4)

For clarity, this is stronger than just taking a rational square root of
the strong equation. A short proof is included. Write the quadratic field's
fundamental integer-coordinate Pell unit as F0+sqrt(F0^2-1), allowing the
usual rescaling of the squarefree discriminant. There are e>=1 and
S=psi_F0(e) such that A=chi_F0(e) and Delta=(F0^2-1)S^2. Then
psi_F0(ep)=Sc and for some u>0,

    |f|=chi_F0(u), I=(F0^2-1)S psi_F0(u).

Let g=gcd(u,ep) and b=psi_F0(g). Strong divisibility and c^2|I give
b>=c/Delta. If g is a proper divisor of ep, then 2g<=ep and

    2b^2<psi_F0(2g)<=Sc<Ac,

contradicting c>A Delta^2. Hence ep|u and u=em with p|m. Composition now
gives the last identity in (4). To see c|m, write m=pt. The recurrence
modulo c^2 gives c|Delta t. Let g0=gcd(c,Delta). The congruence
psi_A(p)=p A^(p-1) modulo Delta implies g0=gcd(p,Delta), so g0|p;
since c/g0|t, it follows that c|pt=m.

In particular (4) proves

    f^2-1=Delta psi_A(m)^2=ic^2 psi_A(m),
    c^2 | f^2-1.                                  (5)

This divisibility must be obtained from rank recovery; it is not valid to
cancel Delta informally in the supplied strong equation.

## 5. Signed auxiliary recovery: no positivity restoration is needed

The auxiliary equation becomes

    I^2 V^2-(I^2-1)y^2=1.

It excludes both V=0 and y=0. Set W=|V| and y0=|y|. Positive Pell
classification at the integer parameter I>1 yields ell>=1 with

    I W=chi_I(ell), y0=psi_I(ell).

The index ell is odd, because chi_I(2r)=(-1)^r modulo I. Write ell=2v+1.
The standard integer polynomials Q_v satisfy

    chi_I(2v+1)=I Q_v(I^2),
    Q_v(1-A^2)=(-1)^v psi_A(ell),
    Q_v(0)=(-1)^v ell.

Thus W=Q_v(I^2). The explicit V has, regardless of the signs of f and T,

    V=-c modulo |f|,
    V=-R modulo c,                                (6)

where the second assertion uses (5). Since I^2=Delta(f^2-1)=1-A^2
modulo |f|, the first congruence implies psi_A(ell)=+c or -c modulo |f|.
Squaring and using the Pell doubling identity gives

    chi_A(2ell)=chi_A(2p) modulo chi_A(m).

The signed chi step-down applies because 0<2p<m, and gives
ell=+p or -p modulo m, hence modulo c. For a self-contained proof, reduce
the index 2ell modulo 2m using
chi_A(j+2m)=-chi_A(j) modulo chi_A(m), then reflect indices above m using
chi_A(2m-j)=-chi_A(j) modulo chi_A(m). The result is a signed representative
of chi_A(r), 0<=r<=m. The case r=m gives residue zero, impossible. A
negative representative cannot equal chi_A(2p) modulo chi_A(m), because
chi_A(r)+chi_A(2p)<=2chi_A(m-1)<chi_A(m). Hence the sign is positive and
strict growth gives r=2p. Thus 2ell=+2p or -2p modulo 2m, as claimed.
Meanwhile I is divisible by c^2,
so the last polynomial identity and the second congruence in (6) give
ell=+R or -R modulo c. Therefore R=+p or -p modulo c. The strict bounds
0<p,R<c/2 exclude the negative case and all nonzero multiples of c:

    p=R.                                          (7)

This argument has not asserted V>0, T>0, f>0, or positive reconstructed
o,j. In particular the fixed-minus parity lemma for positive V is not
being applied to signed V. The residue R=3 modulo 4 will instead follow
from the low compiler masks after population recovery.

Now (2), E>R+2 and n<p=R imply v=0. If epsilon=-1, then p=2n+1.
With Q=chi_A(2)>P0, Pell duplication gives

    psi_A(2n)=2A psi_Q(n)>=A k,

and hence c=psi_A(2n+1)>k(Y+1), contrary to the strict interval
kY<c<k(Y+1). Thus epsilon=1 and nu=1. For the product, Nt=1 now also
excludes C=0. Both versions have

    p=R=2n-1, R odd, C>0.                         (8)

The integer h is automatically positive. If h<=-1 then
k=R+1+hE<R+1-E<0. If h=0, then k=R+1, whereas n>=24 and P0>A>R give
k=2psi_P0(n)>=4P0>R+1. Both are contradictions.

## 6. Signed main-root recovery and automatic gamma positivity

Let R=2r+1, so r>=24. The elementary bounds

    psi_A(2r+1)>=(2A-1)^(2r),
    psi_P0(r+1)<=(2P0)^r

and the strict inequality

    (2A-1)^2/(2P0)>(X+1)^2/X>X

imply c/k>X^r/2. Together with c/k<Y+1 this gives

    Y>X^r/2-1>X^r/3>2^R.                         (9)

The final comparison follows from X>=q>=16 and r>=2:
16^r/3>2^(2r+1). The displayed rational inequality can be checked without
asymptotics by expanding its cross-products; the remaining positive
difference is 12XY(X+1)+9X-2(X+1)^2.

Modulo H=4a+3, the two Pell projections satisfy

    chi_A(j)-a psi_A(j)=2^j,
    chi_A(j)+a psi_A(j)=2^(-j).                    (10)

For the second identity, H is odd and
2(2a+2)=1 modulo H; equivalently the two projections multiply to 1
modulo H, since Delta=a^2 modulo H.

If D<0, then the supplied identity D=X+ac+gamma H and |D|=chi_A(R)
give X=-2^(-R) modulo H. Thus X2^R=-1 modulo H. But (9) gives

    0<X2^R<XY=E<a<H-1,

which is impossible. D=0 is already excluded by the main norm. Therefore
D>0, and the first projection in (10) gives X=2^R modulo H. Both X and
2^R lie in (0,a), so

    X=2^R.                                        (11)

Finally

    D-ac=2c-psi_A(R-1)>c>Y>X,

and hence gamma=(D-ac-X)/H>0. This proves the signed main-root lemma
without assuming gamma positivity in any earlier step.

## 7. Recover the compiler and prove completeness

Since X=wq is a power of two, q=2^u. The bound R>3q implies R>3u, so
q^3 divides X. The proof may therefore rescale w to X/q^3 and apply the
post-index half-binomial ratio calculation with the symmetric scale.
That calculation depends only on the already established indices, the
strict ratio interval, and the two positive scales, not on signs of the
discarded auxiliary coordinates. It gives

    Y=floor((X+1)^(R-1)/X^((R-1)/2))/2,
    v2(Y)=popcount(R)-2.

As q^3 divides Y, popcount(R)>=3u+2. Since beta=2^d-1 divides q-1,
the order of two gives q=B^N. The exact shifted packing identity and the
native mask population sum now give

    (C-1) AND (MC J+1)=0,
    F AND (MF J-1)=0.

These are the blank compiler masks: Start is forced at the origin and
the globally impossible selector is forbidden. In particular the low
mask bits imply R=3 modulo 4, with no appeal to a positive-V parity lemma.
The existing carry-free convolution, clean-band synchronization, anchor,
and blank-run extraction proof then recovers a halting K215 computation.

For completeness start from the canonical positive blank compiler
witnesses of package 06. Replace its normalized strong coordinate by

    i_ordinary=Delta i_normalized.

Every other coordinate, and the auxiliary coefficient, is unchanged:
Delta(f^2-1)=(i_ordinary c^2)^2. This gives a positive zero of (P).
After (11), w=2^R/q>q>F. Therefore

    (K+w)C-F>0,

and the old transport equality implies z_old>=2. Thus
z=z_old-1 is strictly positive and supplies (S). Conversely a solution
of (S) gives a solution of (P) by z_old=z+1; the preceding unit recovery
proves the reverse correspondence on product zeros. The positive and
expanded signed domains all have the same existence condition.

The ultimate Con(ZFC) statement follows by composing this ordinary
compiler proof with the established K215 blank-halting/refutation
calibration. It is not inferred from the soundness of Lean itself.

## 8. Degree certificates and integer conversion

Put Q=beta J and k0=eta+zeta. The product's leading homogeneous form is

    8 Q^55 h gamma i^2 k0^9 w^7 s^16 T^2 f^4
       [w(Q-F-alpha)-z_old Q].                    (12)

It has degree 99. For example the monomial

    J^56 h gamma i^2 eta^9 w^7 s^16 T^2 f^4 z_old

has coefficient -8 beta^56, nonzero for every valid compiler. The main
norm's cancellation is handled by expanding

    (ac+X+gamma H)^2-(a^2+H)c^2
      =2ac(X+gamma H)+(X+gamma H)^2-Hc^2.

The sole degree-28 residual is the auxiliary norm; its leading form is
k0^2 w^2 s^4 Q^14 T^2 f^4. Thus the 77-operation sum of six squared
residuals has exact degree 56.

Every positive integer is represented by

    Pos(u,v,t)=1+u^2+v^2+t(t+1),  u,v,t in Z.

The expression is always positive. Conversely Legendre's three-square
theorem applies to 4n-3 for n>=1; its residue modulo 4 is 1, so exactly
one of the three squares is odd. Write it as (2t+1)^2 and the two even
squares as (2u)^2 and (2v)^2. Dividing by four gives Pos(u,v,t)=n.

Replace each of the nine positive coordinates in Section 2 by a disjoint
Pos expression and leave the other six coordinates unrestricted. This
gives 9*3+6=33 unrestricted integer variables. Each Pos costs seven
binary arithmetic gates, so the product costs 69+63=132 and the sum of
squares costs 77+63=140.

The degrees are better than naive doubling. Assign weight two to the nine
guarded coordinates and weight one to the six signed coordinates. The
six product factors have exact weighted degrees

    44,35,50,13,4,44,

so the unrestricted product has exact degree 190. Its highest form is
(12) with each guarded variable replaced by the homogeneous quadratic
u^2+v^2+t^2. The substitution is injective (set each v=t=0 and use the
monomial map x->u^2), so this highest form does not vanish. For the sum of
squares the auxiliary residual uniquely has highest weighted degree 50;
its square proves exact degree 100. The unrestricted six-equation system
costs 123 operations and has maximum degree 50.

## 9. Reproduction and proof boundaries

Run `python3 build_improved.py` in this directory. It reconstructs all six
circuits from the literal baseline67 JSON, validates every operand and
live gate, checks the operation counts, verifies 100 signed integer or
rational evaluations against independently written formulas, checks the
transport shift and strong/restoration identities, and performs two
modular univariate degree diagnostics per packet. It also checks 96
integer-substitution cases. `python3 -O build_improved.py` is safe because
all checks use explicit exceptions rather than assertions.

These finite computations corroborate the displayed polynomial identities
and degree certificates. They do not prove the Pell rank theorem or the
native compiler, expand its astronomical coefficients, or decide the
existence of a solution. The unproved formalization obligation remains the
entire machine-to-Diophantine bridge, including its inherited compiler.

Principal inherited proof references:

- package 06, `proofs/fixed_blank_67_proof.md`;
- package 02, `FIXED_INPUT75_ORDINARY_PROOF.md`;
- `Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md`;
- `Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md`;
- `Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md`;
- `Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md`.
