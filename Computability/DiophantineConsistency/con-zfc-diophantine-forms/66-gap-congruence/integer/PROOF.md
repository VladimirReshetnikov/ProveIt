# Degree-separated coding with a congruence-separated two-root finalizer

## Scope and exact output

The delivered JSON is one polynomial in ten unrestricted integer variables
`t,g0,h0,k0,l,w,x,y,z,m`. All other symbols below abbreviate polynomials.
The current metrics and exact-degree certificates are in `generated/METRICS.json`
and `CHECKS.json`. The source is specified by `data/layout.json`, the source
file it names, and the complete four-port payload binding. This is an ordinary
mathematical equivalence proof formalizable in ZFC, not a new proof-assistant
certificate. It neither asserts Con(ZFC) nor decides consistency.

The inherited positive31 compiler theorem equates a common positive source
zero to a finite syntactic ZFC refutation. Two reversible row operations and,
where selected, the positive coordinate-gap maps in `upstream/GAP_SOURCE_PROOF.md`
preserve that existence statement. The degree-separated coefficient identity
and the bridge used below are individually identified dependencies. No port
from a different native compiler is substituted into the four-port tuple.
In the primary mirror layout, row2 is also multiplied by -1. This invertible
row orientation preserves the common zero set; rho_j below denotes the
oriented row, exactly as recorded by `row_orientations` in the layout JSON.

## 1. Source and a new one-bit carry deletion

Let W=max(w_i), H=max_d(deg D_d+dW), n=31, and number of target positions=22.
Every w_i is strictly positive and the targets are distinct. The finite
certificate gives the polynomial identities

    [T^q_j](D2(T) U_p(T)^2+D1(T)U_p(T)+D0(T))=2 rho_j(p),
    U_p(T)=sum_i p_i T^w_i.

The weights and kernels are literal data, not unspecified search outputs.
For a source coefficient c_alpha, the corresponding kernel weight is 2c_alpha
in degrees zero and one, and c_alpha product(alpha_i!) in degree two.
Every coefficient has absolute value below M=2^2134927. Set

    kappa=2134940, lambda=2^kappa=8192M,
    b=6t+4, g=b g0, h=b h0, k=b(3k0+2), B=lambda b^2,
    ell=sum_i B^w_i, u=ell+g,
    Gcode=D2(B)u^2+D1(B)u+D0(B),
    AT=sum_j B^q_j, n0=B^(W+1), n1=B^(H+1), N=n0 n1,
    mask=n0-1-(b-1)ell,
    Jcode=2Gcode+AT, Sc=g+n0 Jcode,
    Tc_old=mask+n0(B-2)AT, Tc=Tc_old-2,
    X=N(Sc+Tc+1)-Sc-1,
    Y=2^(16 kappa-23) b B^(H+2W+9), cap=b B^W.

These are all ordinary polynomials with fixed nonnegative exponents. In
particular, the fixed threshold coefficient is supplied as an actual integer.
Its precomputation is outside the variable arithmetic-circuit count.

For all signed assignments b is nonzero, even, and 1 modulo3. B,N,n0 are
divisible by b^2. The low word ell is divisible by B. Consequently

    X is odd, b|(X+1), b|Y, X=0 modulo3.

For the last assertion B=N=n0=1 modulo3, ell=31 and AT=22 modulo3.
Thus mask=0, Tc_old=-22=2, Tc=0 modulo3; the leadless formula gives X=Tc
modulo3. This calculation is valid before positivity or any square condition.

Now assume b is a positive even square and 0<g<2cap. Then b>=4, g is a
multiple of4, and all source coefficients retain their exact bound. The primary mirror certificate has positive leading coefficients in all
three kernels. Each D_d(B)>0 follows by domination of the lower coefficients
for B>M+1, so Gcode>0. The lower-cost companion instead has positive leading
quadratic coefficient and gaps deg D2+W-deg D1>0 and
deg D2+2W-deg D0>0; since u>=B^W, quadratic domination gives the same result. Also
ell<2B^W and u<3bB^W. If Z=B^(H+1), geometric bounds give

    |Gcode| < 13 M b^2 Z/(B-1),
    0<Jcode<Z/128.

The selected target headroom H-max(q_j)>=2 makes
(B-2)AT<Z/B^2. Along with g<n0, mask<n0, this gives
0<Sc, 0<Tc_old and Sc+Tc_old<N. The subtraction of2 preserves
nonnegativity, since the entire base-B low digit of Tc_old is B-1 and B>=4.
Thus Sc+Tc<N and X>=N-1>3b. Likewise Y>max(b,256).

When b=2^s, B=2^v with v=kappa+2s, the low bit1 of Sc is zero:
g is a multiple of4 and n0 is a multiple of4. The same bit of Tc_old is one,
because its low base-B digit is B-1. Hence

    Sc AND Tc = Sc AND Tc_old,
    pop(Tc)=pop(Tc_old)-1=(W+23)v-31s-23.

This is why no extra factor4 is required on the packing word. The argument
uses square-base recovery before digit decoding; it does not assume 4|b on
all signed assignments.

Write N=2^u0. The two disjoint blocks of
X=(Sc+Tc)N+(N-1-Sc) give exactly

    pop(X)=u0+pop(Tc)-[pop(Sc)+pop(Tc)-pop(Sc+Tc)].

The bracket is nonnegative, vanishing exactly when Sc AND Tc=0. Moreover
u0=(H+W+2)v, so the maximum population is

    (H+2W+25)v-31s-23 = log2(Y).

The factorial valuation identity therefore proves
Y divides binomial(2X,X) iff Sc AND Tc_old=0. The inherited signed-borrow
argument now gives exactly a positive common source zero, since the low mask
decodes g=sum_i(p_i-1)B^w_i and the positive word is u=ell+g.

Conversely a positive source zero can be encoded for every sufficiently large
b=4^s. Its all-one tuple is not a zero (row5 evaluates to1), so g>0. All
weights are positive, giving b^2|g and b<=g<cap. Thus the imposed normalization
g=bg0 loses no canonical witnesses. Deleting the top block and bit1 reduces
the old exact threshold by4; it is not an uncalibrated deletion of terms.

## 2. Division-free bridge registers and polynomial

Put

    L=lY, U=2LX, V=4gwY, Wb=bw, A=U(V+1), B1=2X+1,
    C=B1+(A-2)h, Phalf=(LX)UV, P=2Phalf,
    K=X+1+k(P-2), S=2A-5, T=3Wb C-2(Wb^2-1),
    Q=(Phalf^2-1)K^2+1,
    Delta=8cap^3 gK^2-g^2[32(C-KL)^2cap^3+g^2K^2],
    xi=zx, D=(A^2-4)C^2+4, E=C^2Dxi,
    F=4(A^2-4)E^2+1,
    G=2(A+2)(A-2)^2E^2-1,
    Omega=16E, Hc=C+(B1-C)F+Omega F y,
    I=(G^2-1)Hc^2+1,
    Sigma=xi S^5, rho=T+Sy,
    Theta=(rho^3-rho S^2-S^3)(rho^2+23S^2),
    r=bQ, a=r+(3Delta-1)(rz)^2, d=DFI, Z=Sigma m-Theta.

The single equation is

    F10=(Z^2-Sigma^2(a+d))^2-4Sigma^4 a d=0.

The emitted evaluator uses the exact factorizations
G=(A/2-1)(F-1)-1 and Hc=C+F(B1-C+Omega y), with the division-free
register A/2=(LX)(V+1). These are identities, not rational operations.

The inherited Sun bridge is stated in `upstream/CONGRUENCE_FINALIZER.md`,
Sections3 and7, with its primary theorem references. The reverse input is:
b square, f_old^2 l^2 Delta>0, xi!=0, 4Q and DFI squares, S|T,
and the source size/congruence bounds; here f_old=2t+1 is automatically nonzero.
The forward theorem supplies the exact Lucas values C=u_(2X+1)(A) and
K=u_(X+1)(P), and the modified certificate permits prescribed divisibility
of xi and arbitrary residues of y. These are essential hypotheses and are
not replaced by finite tests.

## 3. Unconditional congruence separation and soundness

From the formulas, 2b|U,A and 3|P. The latter uses 3|X. The restrictions on
k imply b|K and 3|K. Thus Q=1 modulo b^2 and modulo3. In particular Q is
odd and coprime to b. The restriction on h and b|(X+1) give 2b|(C+1),
and hence 4b|D. Therefore, on every integer assignment,

    a/b is odd, d/b is even, and a!=d.

No positive-radicand assumption is made here. S is odd and nonzero.
The rational-root-free quintic pi(t)=(t^3-t-1)(t^2+23) gives Theta!=0.
If Sigma=0 then F10=Theta^4!=0. At a zero Sigma!=0 and q=Z/Sigma satisfies
(q^2-a-d)^2=4ad. Since a!=d, q!=0; the rational numbers

    u=(q^2+a-d)/(2q), v=q-u

satisfy u^2=a,v^2=d. Rational square roots of integers are integers.
Consequently a,d are squares and Sigma|Theta. The usual prime-valuation
argument for S^5|Theta yields S|T.

Factor a=r[1+(3Delta-1)rz^2]. The two factors are coprime and nonzero,
and r=1 modulo3. As their product is a square, both are positive squares:
negative squares cannot be1 modulo3. The same reasoning applied to
r=bQ, using gcd(b,Q)=1 and b=Q=1 modulo3, makes b and Q positive squares.
Since b is even, b>=4. The second factor would be negative if Delta<=0,
so Delta>0. Its defining formula gives K!=0 and 0<g<2cap. If l=0 then
P=0 and Q=1-K^2<=0, impossible. Thus l!=0 and f_old^2 l^2 Delta>0.

The source bounds from Section1 now hold. All reverse bridge hypotheses
are established in the required order, and the resulting binomial
divisibility decodes a common positive source zero. No sign condition on an
arbitrary auxiliary input was silently assumed.

## 4. Completeness, including the imposed congruence classes

Begin with a positive source zero and choose a sufficiently large b=4^s,
s>=1. Set t=(b-4)/6 and g0=g/b. The source construction has b^2|g and
X+1=-g modulo b^2. Apply the constructive Sun bridge. Since X is odd,
X+1 is even. The Lucas recurrence makes K=u_(X+1)(P) divisible by P,
and 4b^2|P. In (P-2)k=K-X-1, the right side is divisible by b^2 while
v2(P-2)=1, proving b|k. Modulo3, P=X=K=0 implies k=2. Thus k/b=2 modulo3
and k has the required form b(3k0+2).

For C=u_(2X+1)(A), odd X implies C+1=0 modulo A^2. Here 4b^2|A^2 and
2b^2|(B1+1), so 2b^2|(C-B1). Since v2(A-2)=1, h=(C-B1)/(A-2)
is divisible by b. This proves the imposed form h=bh0 without a new
cofinality assumption on h or k.

Now b,Q are positive squares and Delta>0. The integer delta=3Delta-1 is
positive, 2 modulo3 and nonsquare. Thus delta*r is positive nonsquare.
Pell's theorem supplies u,z>0 with u^2-delta*r*z^2=1, so a=ru^2 is square.
The modified Lucas interpolation chooses xi divisible by this z and y in
a class with pi(T/S+y)=0 modulo xi, while retaining d square. The quintic
has a root modulo every positive integer; its cubic discriminant is -23,
and its quadratic factor supplies the complementary local roots, with
Hensel lifting and CRT. Put x=xi/z and
m=Theta/Sigma+sqrt(a)+sqrt(d). These are integers and F10=0.

The inherited source/refutation equivalence therefore gives, in ZFC,
absence of integral zeros of this explicit F10 iff Con(ZFC).

## 5. Exact degree, costs and verification boundary

Let rX=deg X=4(W+H)+6 and rY=deg Y=2H+4W+19. Positive source leading
coefficients prove these degrees are attained. Then aA=deg A=rX+2rY+4.
Degree propagation gives

    deg D=4aA+4, deg F=14aA+20,
    deg G=15aA+20, deg Hc=20aA+31,
    deg I=70aA+102, deg d=88aA+126,
    deg Sigma=5aA+2.

The unique dominant final term is Sigma^4 d^2; neither the guard nor the
center reaches that degree. Explicitly, with ccap=2W+1 and
pdeg=2rX+3rY+5, the guard has degree at most
4aA+8pdeg+3ccap+16=20rX+32rY+3ccap+72, strictly below
88aA+126 for the displayed positive W,H. The center has degree5aA+20.
These inequalities make Sigma^2 d uniquely dominant in the inner square
and Sigma^4 d^2 uniquely dominant after the final subtraction. Thus

    deg F10=196aA+260=2352W+1568H+9668.

The independent checker propagates upper degree and the coefficient at that
degree along the full diagonal, modulo three primes using the actual fixed
coefficients. A nonzero coefficient proves the upper bound is attained;
this is not a sampled lower degree presented as an upper bound. It also
checks every isolation interaction, all literal coefficients, the complete
DAG against a separate formula, unconditional congruences, and the carry
identity. None of these finite audits is substituted for the proof above.

The incoming code computes the constant threshold from two fixed leaves in
five gates. This delivery materializes their product as one fixed integer,
so those five gates are not charged to variable evaluation. This convention
is disclosed; adding five restores that historical evaluator convention
without affecting the polynomial, proof, or exact degree.

Primary mathematical references:
- Z.-W. Sun, Further results on Hilbert's Tenth Problem, Theorems4.12--4.13,
  https://arxiv.org/html/1704.03504v7
- Z.-W. Sun, Ten unknowns for Hilbert's tenth problem over the integers,
  Theorems3.1,4.1 and Propositions6.1--6.2,
  https://arxiv.org/html/2609.01594v1

These pages were directly checked during preparation. Exact coefficient
payloads, compiler proofs, layout certificates and source pins are retained
with the package; no merely existential universal-polynomial coefficient
stands in for the actual integers.
