# A smaller certified packing for the nine-positive-variable equation

This appendix improves the literal degree-separated/free-coordinate equation
of package 59 at ProveIt commit `beb0192cb8dc36f78c369c080f2adfbc1887a486`.
It uses the same complete native coefficient tuple and the same nine-variable
arithmetic finalizer. The new ingredient is a smaller finite isolation layout
and a sign change of one source equation. This is a finite combinatorial
improvement, not a new universal variable bound or an absolute simplicity claim.

The resulting polynomial has nine strictly positive integer unknowns,
exact total degree **1,781,068**, and **470** live binary arithmetic operations
(162 additions, 22 subtractions, 286 multiplications). Package 59's corresponding
point is degree 1,910,404 and 473 operations. All literal leaves are supplied.

## 1. Fixed source and exact polynomial

`data/parent_source.json`, SHA256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`,
lists 31 positive coordinates and 22 quadratic residuals r_j. The fixed ports
are beta, K0, MC, MF. They are the *complete* original package-31 tuple,
`wang943-mixed-121x8801`, with K0=K and the already-shifted MF=MF_source.
The four compressed integer payloads and their exact digests are under
`coefficients/`; the finite native generator and its literal 430-action input
are under `native/`. Regeneration independently matched all four payloads.

Replace r14 by r14+r2, replace r15 by r15+r3, and replace r22 by -r22.
Call the resulting rows rho_j. These invertible integer row operations preserve
the complete positive common zero set. All other rows are unchanged.

For the ordered source coordinates, the new positive digit positions are

    110,105,100,94,74,22,41,95,87,89,49,31,11,16,98,19,
    97,4,20,8,2,3,35,47,111,30,90,63,78,103,26.

The target assignments, as (row,target), are

    (10,26),(5,39),(2,251),(4,267),(6,299),(1,510),(3,514),
    (9,567),(15,769),(20,838),(21,899),(13,930),(18,1123),
    (16,1184),(11,1191),(12,1262),(17,1422),(19,1423),
    (7,1490),(14,1707),(8,1767),(22,1954).

For a monomial y^alpha in rho_j of degree d=0,1,2 and coefficient a_j,alpha,
put e(alpha)=sum_i alpha_i*w_i. Define its kernel coefficient to be twice
a_j,alpha for degrees 0 and 1; for degree 2 use
a_j,alpha*product_i(alpha_i!). Define

    D_d(Z)=sum_{j,|alpha|=d} c_j,alpha Z^(q_j-e(alpha)),
    U_y(Z)=sum_i y_i Z^w_i,
    G(Z,y)=D_2(Z)U_y(Z)^2+D_1(Z)U_y(Z)+D_0(Z).

All exponents are nonnegative. The literal kernels are supplied in
`data/split_kernels.json`. Exact enumeration of the 1, 31 and 496 monomials
of degrees 0,1,2 respectively verifies every one of 22,544 interactions.
There are precisely 89 intended contributions and no contamination at targets.
The multinomial coefficients give, identically in all source coordinates
and all four ports,

    [Z^q_j]G(Z,y)=2*rho_j(y).

The new measurements are W=111, target maximum 1954, kernel degrees
(1954,1617,1788), and convolution height H=2010. The top term of D2 is
exactly +Z^1788. This comes from the +g*Baux term of -r22. Negating r22
therefore preserves solvability while making the highest quadratic layer
positive. No variable or coefficient port is changed.

## 2. Positivity before digit decoding

Every weighted kernel coefficient has absolute value below M=2^2134927.
This follows by recomputing the original conservative port-bit majorant;
row signs do not affect it. Put a=2^2134939=4096M and B=a*b^2.
Let ell=sum_i B^w_i and U=ell+g. For every b,g>=1,

    U>=B^111,
    D2(B)>B^1788*(1-M/(B-1))>B^1788/2,
    |D1(B)|<2M*B^1617,   |D0(B)|<2M*B^1954.

Relative to B^1788 U^2, the last two possible negative contributions are
less than 2M/B^282 and 2M/B^56. Each is less than 1/8. Consequently

    G(B,U)>B^1788 U^2/4>0

before any binary-base, source-solution or bounded-digit assumption.
This replaces, rather than blindly reuses, package 59's positivity estimate.

Let Targ=sum_j B^q_j, N0=B^112, Z=B^2011. Define

    Mask=N0-1-(b-1)ell,
    Jcode=2G(B,U)+Targ,
    S=g+N0*Jcode,
    T=Mask+N0*(B-2)*Targ,
    t=bB^111,  Gcap=32t.

The low mask lies in [0,N0), and S,T are nonnegative for all positive b,g.
On the entire soundness range g<4bB^111, U<6bB^111. The geometric-series
coefficient estimate, keeping its denominator rather than replacing it by 2,
gives

    2G/Z < 86M*b^2/(B-1) < 1/32.

Indeed 86*32<4095. The target maximum 1954 is 56 below H, so both
Targ and (B-2)Targ are less than Z/64. Also g<N0. Thus S+T<N0*Z=B^2123.
These estimates are valid before B is proved a power of two.

When b is a power of two and g is in this range, low-mask decoding gives
g=sum_i n_i B^w_i with 0<=n_i<b, and U encodes
y_i=n_i+1. The coefficient bound is

    |[Z^e]G| <= M*((sum_i y_i)^2+sum_i y_i+1)
              <=993M*b^2 < B/4.

There is at most one coefficient at each exponent within each homogeneous
kernel, so this estimate controls unmarked collisions as well. The inherited
sparse-borrow padding lemma now applies exactly as before: S&T=0 precisely
when g encodes a common positive source zero. The original row5 is unchanged
and equals 1 at the all-one tuple, so a source zero has a nonzero digit,
g>=B>0. Every source zero can be encoded for every sufficiently large binary b,
and its code satisfies g<bB^111, hence 32g<Gcap.

## 3. Exact recalibration of the two-block number

The changed block length and valuation threshold are

    L=2*b*B^2123,
    R=L*(S+T+1)-S-1,
    c=2^16012032,
    N=c*B^1121.

The factor 2 in L and the absence of a factor b in N are essential. For all
positive outer assignments R>=L-1>=8, N>=8 and b<=R,N. On the bounded branch
S+T<B^2123<L. If b=2^k, B=2^v, then v=2134939+2k and
u=log2 L=1+k+2123v. The disjoint two-block identity is

    R=(S+T)L+(L-1-S),
    pop(R)=u+pop(T)-tau,
    tau=pop(S)+pop(T)-pop(S+T)>=0.

The low-mask population is 112v-31k; each of the 22 high target masks B-2
has population v-1. Hence pop(T)=134v-31k-22 and

    u+pop(T)=2257v-30k-21
            =2242v+32024064
            =2*(1121v+16012032)=2*log2 N.

The middle equality uses 15*2134939-21=32024064. Legendre's formula yields

    N^2 divides binomial(2R,R)  iff  tau=0  iff  S&T=0.

The calibration includes b=1. That case cannot produce a final zero, since
Mask=N0-1 and 0<g<4B^111<N0, whence g&Mask=g>0.

## 4. The final nine-variable equation

Use the nine strictly positive variables b,g,h,s,w,C,i,j,n and put j0=j-1.
Define the following polynomial registers (none is a new quantified variable):

    U=N^2*w,  Y=N^2*s,  M0=R*Y,
    P=2*M0^2*U,  K=R+1+h*(P-1),  A=M0*(U+1),
    B1=2R+1,  W1=b*w,  J=4A-5,
    Q=3W1*C-2*(W1^2-1),
    D=(A^2-1)*C^2+1,  k0=i*J*C,  E=k0*D*C,
    F=(A^2-1)*E^2+1,
    G=A+F*(C*D+1-A),  H0=C+F*(B1+j0*C),
    I=(G^2-1)*H0^2+1,
    a0=(P^2-1)*K^2+1,  a1=D*F*I,
    m=K^2*(4t-g)-16t*(C-KY)^2,
    V0=P*K,  Tpair=k0*(8D^2-4D-1),  V1=Tpair*G*H0,
    Omega=J*m,  E0=J*(n+W1^2)+Q,
    Theta=E0-Omega*(V0+V1).

The equation is

    F9 = [Theta^2-Omega^2*(a0+64a1)]^2 - 256*Omega^4*a0*a1 = 0.

It has one polynomial output and nine positive unknowns. The complete
division-free evaluator is `generated/split_111_positive.json`.

The algebraic finalizer and its ordinary proof are inherited unchanged from
package 59's free-coordinate adjunct, retained in `upstream/FREE_NINE_PROOF.md`.
Their hypotheses are precisely the unconditional R,N,b inequalities,
the source bound 32g<Gcap for completeness, and the binary-mask equivalence
on the returned soundness branch 8g<Gcap. All have just been reproved for
this new layout. The positivity-first proof of m>0, recovery of the old C
range, exact CRT substitution j0=j-1, radical integrality and final positive
n therefore apply without a new cofinality assumption. In particular no
arbitrary old witness is silently restricted to a smaller residue class.

Combining with the inherited positive-source compiler and K215/refutation
calibration gives the ordinary mathematical theorem formalizable in ZFC:

    ZFC proves: (there is no positive zero of F9) iff Con(ZFC).

No consistency assumption is used. This is not a new end-to-end Lean/Rocq
proof or exported object-language ZFC derivation. Its unbounded imported
theorems are distinguished from the finite certificate checks.

## 5. Exact degree and gate count

The new source leading degrees are deg(S)=4244, deg(T)=4134, deg(L)=4247,
deg(R)=8491 and deg(N)=2242. On the all-input diagonal the respective R,N
leading coefficients are 4*a^4245 and c*a^1121. Write r=deg(R), q=deg(N),
and d=deg(A)=r+4q+2. The same exact cancellation resolution as in package59
gives

    Delta1=V1^2-64a1
           =[(8D+1)k0^2-64D]*(G*H0)^2+64DF*(H0^2-1),
    Theta^2-Omega^2*(a0+64a1)
       =E0^2-2E0*Omega*(V0+V1)
        +Omega^2*((K^2-1)+Delta1+2V0*V1).

The unique leading term of the inner expression is Omega^2*Delta1, of
degree 50d+2r+4W+58. Its square has strictly higher degree than the final
subtracted term, by 28d+44. Therefore the exact degree is

    104r+400q+8W+316 = 816H+1224W+5044 = 1,781,068.

The diagonal leading coefficient is the positive integer
2^290*a^890324*c^400, so the multivariate upper bound is attained for the
actual native tuple. The degree certificate resolves cancellations; the
degree is not a naive maximum propagated through the unreduced norm.

The primary DAG uses 470 live gates; constant-only arithmetic is folded,
fixed integer leaves and register reuse are free, while every live binary
addition, subtraction and multiplication (including scalar multiplication)
is charged. The natural-coordinate companion shifts all nine input domains
appropriately, has the same degree, and costs 477 gates. These are circuit
metrics, not bit-complexity bounds or optimal-circuit lower bounds.

## 6. Reproduction and attribution

Run `python3 build_nine.py`, `python3 materialize_fixed.py`, and
`python3 verify_candidate.py`. `native/build_coefficients.py` independently
regenerates the four source ports from literal data. The exact finite packing
certificate is the proof dependency; heuristic search is not.

New layout and independent audit: this research iteration. Degree-separated
kernels and the free-coordinate arithmetic tail: ProveIt package59; free Pell
coordinates and the shorter binary block originate in package56. The circuit
builder is adapted from package59 and the small DAG implementation from
package53. Native coefficient generator and inherited compiler proof:
package31. Retained third-party notices are under `native/licenses/`.
