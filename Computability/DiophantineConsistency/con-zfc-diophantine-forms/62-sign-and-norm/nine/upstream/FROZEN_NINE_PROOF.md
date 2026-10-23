# Degree-separated, parity-calibrated nine-variable equation

## 0. The result, domains, and trust boundary

The primary division-free circuit is `generated/split_116_positive.json`.
It has exactly **nine strictly positive integer unknowns**, exact total degree
**2,676,548**, and **476 live binary arithmetic operations**: 164 additions,
23 subtractions, and 289 multiplications. Every fixed power is evaluated by
charged multiplications. Fixed integer leaves, including those given by
recipes, are coefficients, not additional unknowns. The independently
translated natural-domain equation is `generated/split_116_natural.json`.

The theorem is: ZFC proves that this equation has a zero in its stated domain
if and only if a finite syntactic ZFC refutation exists. Taking negations gives
the requested equivalence of absence of zeros with Con(ZFC). The imported
semantic premises are the original package31 positive compiler with its
complete coherent four-port tuple, and the numerical Jones ratio theorems
`Jones1982.Nine.ratio_sound` and `ratio_complete`. This is an ordinary
mathematical proof, not a new end-to-end proof-assistant formalization, a proof
of consistency, or a global-minimality claim. There is no unrestricted-integer
nine-variable claim.

Against the frozen wave7 primary degree 7,344,328 and cost 738, the degree
falls by 63.56% and the circuit cost by 35.50%. It also improves both metrics
over every supplied packet52 nine-variable equation. Three composed packet52
source variants remain reproducible comparisons: degree/cost
6,125,108/577, 6,339,380/515, and 9,336,884/475. The last saves one operation
relative to the primary at a much larger degree. We do not call the primary a
strict Pareto improvement over that last, newly composed comparison.

## 1. Bind the compiler before changing its source encoder

Let r_1,...,r_22 be the quadratic residuals in 31 positive variables from
`data/parent_source.json`, SHA256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.
The four ports beta,K0,MC,MF have bit lengths
1,064,921; 1,070,004; 1,064,921; 1,064,922. They are exactly the original
package31 whole tuple, with MF already shifted. They are supplied as minimal
unsigned **little-endian** gzip-compressed payloads in `coefficients/old_tuple`.
The binding gives full raw and compressed hashes, aliases, and the complete
compiler-adapter proof. `upstream/old_tuple_complete_proof.md` states the
unbounded compiler interface being imported. No coefficient from the newer
packet52 tuple is substituted into this source.

The packet52 60-gate presentation is independently expanded in the checker.
It differs from this source only in residual15, by the extra term -beta*J.
The checker verifies that exact difference. Consequently the packet52 source
and tuple are retained as a separate matched pair for the three comparison
circuits, never mixed into the primary equation.

Apply the elementary row operations

    rho_14 = r_14+r_2,    rho_15 = r_15+r_3,

leaving the other rows unchanged. Their inverses subtract rho_2 and rho_3;
thus the common zero set is unchanged. The resulting raw positive-coordinate
system has 89 coefficient records: 7 constant, 39 linear, 43 quadratic.

## 2. Split homogeneous degrees instead of adding a dummy coordinate

The weights in the original variable order are

    1,7,61,36,16,85,20,67,43,11,34,13,96,80,29,50,
    2,109,110,112,116,91,53,55,27,101,92,9,107,37,60.

The row order and corresponding target exponents are

    rows:    2,22,8,15,9,11,3,17,13,18,12,20,4,21,19,1,6,10,16,14,7,5;
    targets: 28,85,286,384,593,602,642,731,906,966,1083,1212,1231,
             1393,1461,1471,1678,1719,1732,1880,2107,2129.

Write W=116. If y^alpha is a supported monomial of rho_j, d=|alpha|, and
e(alpha)=sum alpha_i w_i, weight its coefficient by 2 for d=0,1; for d=2
weight it by product alpha_i!. Put

    D_d(t)=sum_(j,|alpha|=d) c_(j,alpha) t^(q_j-e(alpha)),
    U_y(t)=sum_i y_i t^w_i,
    G(t,y)=D_2(t)U_y(t)^2+D_1(t)U_y(t)+D_0(t).

The exact kernel lists are `data/split_kernels.json`. The certificate
`data/split_code.json` guarantees that a source term in degree d can land at
target q_k against a degree-d monomial only for its own row and monomial.
The 1, 31, and 496 candidate monomials are checked separately. In particular
linear and quadratic labels need not avoid one another: they never multiply
the same kernel. Factorial cancellation gives the formal identities

    [t^q_j]G(t,y)=2rho_j(y).

The checker enumerates all 22,544 interactions and compares the resulting
formal coefficient data. It also proves both inverse row identities. The
kernel degrees are 1719,2027,1929; the leading coefficient of D_2 is +1.
The convolution height is

    Kcode=max(deg D_d+dW)=2161.

The kernels have distinct exponents internally. From the actual port bit
bounds and every exact coefficient recipe,

    |c_(j,alpha)| < M=2^2134927.

Set the explicit fixed integers

    a=4096M=2^2134939,    c=2^17079502.

No variable-exponent operation occurs anywhere.

## 3. Positivity and bounds before any binary-base conclusion

For now use the mixed coordinates b,g,h,s,w,i>=1 and phi,j,n>=0. Define

    B=ab^2, ell=sum_i B^w_i, Us=ell+g,
    Gs=D_2(B)Us^2+D_1(B)Us+D_0(B),
    Targets=sum_j B^q_j, N0=B^117, Z=B^2162,
    Mask=N0-1-(b-1)ell,
    Jcode=2Gs+Targets,
    Scode=g+N0 Jcode,
    Tcode=Mask+N0(B-2)Targets,
    L=2b B^2279,
    R=L(L+Scode+Tcode+1)-Scode-1,
    N=c b B^1201, Gcap=32b B^116.

L is the carry-block size; N is a different square-root threshold passed to
Jones. Their distinction is essential.

For every assignment g>=1, Us>=B^116. Since B>=4096M,

    D_2(B) > (1-M/(B-1))B^1929 > B^1929/2,
    |D_1(B)|<2M B^2027,    |D_0(B)|<2M B^1719.

Relative to B^1929 Us^2, the two negative contributions are less than
2M/B^18 and 2M/B^442, respectively, each less than 1/8. Hence
Gs>B^1929 Us^2/4>0, unconditionally. The low-mask digits are B-b at the
31 weight positions and B-1 elsewhere through W, so 0<=Mask<N0.
Consequently Scode,Tcode>=0 and

    R=L^2+(L-1)Scode+L Tcode+L-1>=L^2+L-1.

It follows unconditionally that R,N>=8, b<=R,N, Gcap>0. No binary-base
assumption and no upper bound on g has been used to justify these hypotheses.

On the branch g<4bB^116, ell<2B^116 gives Us<6bB^116. Distinct kernel
positions and geometric summation give

    |Gs| < M B^2162 (1+6b+36b^2)/(B-1)
          <=43M b^2 B^2162/(B-1).

Because B=4096Mb^2 and B>=4, this implies 2Gs<Z/32. Also
Targets<2B^2129<Z/64 and (B-2)Targets<2B^2130<Z/64.
Thus Jcode<3Z/64, while g<N0 because 4b<B. Since Z>128,

    Jcode+(B-2)Targets+2 < Z,
    Scode+Tcode < N0 Z = B^2279 < L.

All subsequent finite-word manipulations are therefore legitimate before
the arithmetic theorem identifies B as a power of two.

## 4. Recover positive source digits with sparse +1 padding

Suppose b=2^k is a power of two, allowing k=0. Then B=2^v with
v=2134939+2k. On the bounded-g branch, the low binary-disjointness condition

    g & Mask = 0

is equivalent to g=sum z_i B^w_i with 0<=z_i<b. Put y_i=z_i+1. Then
1<=y_i<=b and Us=sum y_i B^w_i, exactly the positive-coordinate word.
For every coefficient h_t of G(t,y), including unsupported collisions,

    |h_t| < M[(sum y_i)^2+sum y_i+1] <=993Mb^2 < B/4.

Therefore Jcode has signed base-B digits 2h_t+delta_t, where delta_t=1
at the marked targets and 0 elsewhere. With incoming borrow e_-1=0,
normalization gives outgoing borrow e_t in {-1,0}. At a marked cell its
normalized digit is (2h_t+1+e_(t-1)) mod B. This avoids the mask B-2 exactly
when h_t=0: zero gives 0 or1; positive h_t gives a digit between 2 and B/2;
negative h_t gives a digit strictly greater than B/2. These ranges follow
from the strict B/4 bound and include both borrow choices.

Because Jcode>0 and Jcode<Z, this is ordinary finite binary disjointness.
The low and high blocks do not overlap. Thus

    Scode & Tcode = 0
      iff g encodes y_i=z_i+1 with rho_j(y)=0 for every j.

Conversely, a positive source zero y yields z_i=y_i-1>=0. Choose any
sufficiently large power of two b>max y_i and set g=sum z_i B^w_i. The
all-one source tuple is not a zero, since r_5(1,...,1)=1. Thus g>0. The
usual sparse-digit bound gives g<bB^116 and hence 32g<Gcap. Every
sufficiently large power of two is admitted; no sparse-cofinality assumption
or extra unknown is required.

## 5. Parity calibration with the even target parameter

For 0<=S,T and S+T<L=2^u, define

    X=L^2+(S+T)L+(L-1-S).

Its three nonoverlapping words give

    pop(X)=u+pop(T)+1-[pop(S)+pop(T)-pop(S+T)].

The bracket is nonnegative, and it vanishes exactly when S&T=0. Legendre's
formula says v_2(binomial(2X,X))=pop(X). For the present Tcode,

    pop(Tcode)=(117+22)v-31k-22=139v-31k-22,
    u=1+k+2279v.

Hence the exact tested exponent is

    u+pop(Tcode)+1=2418v-30k-20.

Unlike the previous odd-parameter layout, 2418 is even. The factor b already
present in N resolves that parity without restricting b:

    2log_2(N)=2(17079502+k+1201v)=2418v-30k-20.

Therefore

    N^2 divides binomial(2R,R) iff Scode&Tcode=0.

This proves the source contract in both directions with precisely the R,N,
Gcap passed to the ratio theorem. The general calibration implemented for
the comparison layouts is included in the generated metadata and checked
in 540 separate exponent fixtures.

## 6. Exact arithmetic ratio interface and CRT witness substitution

Use the following polynomial registers:

    U=N^2w, Y=N^2s, M0=RY,
    P=2M0^2U, K=R+1+h(P-1), A=M0(U+1),
    B1=2R+1, W1=bw, C=B1+W1+phi,
    J=4A-5, Q=3W1C-2(W1^2-1),
    D=(A^2-1)C^2+1, k0=iJC, E=k0DC,
    F=(A^2-1)E^2+1,
    G=A+F(CD+1-A), H=C+F(B1+jC),
    I=(G^2-1)H^2+1,
    a0=(P^2-1)K^2+1, a1=DFI.

The old ratio witness is H_old=B1+j_old C, j_old>=1, with condition
JF | QF+J(H_old-C). Since F=1 modulo J and C, this condition is exactly
J|Q and F|(H_old-C). The quotient z=(H_old-C)/F is positive and is B1
modulo C. As 0<B1<C, z=B1+jC for a unique j>=0. This gives the displayed
H. Conversely j_old=1+((F-1)/C)B1+Fj is a positive integer with the same H.
Thus the reparameterization is exact, not merely cofinal.

Normalize the old margin by its known factor8:

    t=b B^116,
    m=K^2(4t-g)-16t(C-KY)^2.

Then 8m=K^2Gcap-4(C-KY)^2Gcap-8gK^2. The two margins have precisely the
same strict sign, and m is an integer polynomial. This removes a scalar
factor from the finalizer without changing the ratio conditions. Those
conditions are now a0 square, a1 square, J|Q, and m>0.

The inherited ratio theorem gives b a power of two, 8g<Gcap, and
N^2|binomial(2R,R). Its bounded branch is g<4bB^116, exactly Section3.
Its completeness theorem uses 32g<Gcap, supplied by Section4. All other
numerical and domain hypotheses were proved before the finalizer was used.

## 7. The sharp Pell majorant and positivity-first norm

All relevant tail registers are positive on every mixed-domain assignment;
A>=2, J>=3, D>C^2, Q>0, and C>W1>=1. Put

    V0=PK, Tpair=k0(8D^2-4D-1), V1=Tpair G H.

The exact identities

    V0^2-a0=K^2-1>0,
    Tpair^2-64DF=(8D+1)k0^2-64D>0,
    Delta1=V1^2-64a1
      =[(8D+1)k0^2-64D](GH)^2+64DF(H^2-1)>0

give strict positive integer majorants of sqrt(a0) and sqrt(64a1).
Here k0>=3, so the middle defect is at least 8D+9. Also
Q<3C^2<3D<Tpair<=V1, hence Q/J<V1.

Define the primary equation by

    Omega=Jm,
    Theta=Jn+Q-Omega(V0+V1),
    F9=(Theta^2-Omega^2(a0+64a1))^2-256Omega^4 a0a1=0.

If m=0, then Theta=Jn+Q>0, so F9 cannot vanish. Otherwise the real
four-factor norm identity supplies real roots r0^2=a0, r1^2=64a1 and

    n+Q/J=mZ,    Z=V0+V1+r0+r1>0.

The strict majorants prove Z>0 without any integrality assumption. The
left side is positive; consequently m>0 is established first.
The original margin inequality now gives C>K(Y-1/2)>K, because Y>=64.
Moreover A^2>P, D>C^2, F>=A^2, G>=A, I>=G^2>=A^2. Therefore

    a1=DFI>C^2A^4>K^2P^2>a0.

The rational signed sum x=Theta/Omega=r0+r1 is nonzero, since 64a1>a0.
The identity 2xr0=x^2+a0-64a1 makes r0 rational and then r1 rational.
Rational square roots of integers are integers. In addition r1/8 is a
rational square root of a1, hence an integer. Thus both ratio radicands
are squares, Z is integral, and n+Q/J=mZ gives J|Q.

Conversely, if the ratio conditions hold, choose positive integer roots
r0,r1 and set n=m(V0+V1+r0+r1)-Q/J. Since m>=1 and V1>Q>Q/J,
this is a positive integer. One real linear factor vanishes, so F9=0.
This completes both implications, without any independence assumption on
the square classes of the radicands.

## 8. Exact total degree, not an upper bound

The main circuit is optimized for size; a separate certificate circuit uses
the exact Delta1 identity to resolve its leading cancellation. With
E0=Jn+Q, the identity is

    Theta^2-Omega^2(a0+64a1)
      =E0^2-2E0 Omega(V0+V1)
       +Omega^2[(K^2-1)+Delta1+2V0V1].

Let r=deg R=9118 and t=deg N=2403. A symbolic diagonal leading-term audit
gives the following degrees, with explicitly nonzero leaders:

    P 32657; K 32658; A 18732; C 9118; D 55700;
    k0 27851; F 222802; G 287620; H 231921;
    a0 130630; a1 1317584; m 75163; Omega 93895;
    V0 65315; V1 658792; Delta1 1150484.

The term Omega^2 Delta1 uniquely dominates the inner expression, of degree
1,338,274. Its square dominates the other norm term, whose degree is
1,823,794. Hence

    deg F9 = 188r+400t+8W+236 = 2,676,548.

Its diagonal leading coefficient is exactly

    2^542 a^1337768 c^400 > 0.

The certificate's multivariate upper bound is thus attained on the diagonal,
proving equality. All positive-degree cancellations have been resolved by
displayed identities; unknown coefficient-dependent heads are never guessed.

## 9. Positive and nonnegative equations, and reproducibility

The nine positive inputs are b,g,h,s,w,phi_plus,i,j_plus,n_plus. The circuit
uses phi=phi_plus-1, j=j_plus-1, n=n_plus-1, leaving the other six inputs
unchanged. In its JSON those positive input names are shortened to phi,j,n;
the domain annotation and shifts are authoritative. The natural-domain
circuit instead shifts b,g,h,s,w,i upward by1. These are bijections with the
mixed domain, and affine translations preserve total degree.

Run `python3 nine/build_nine.py` and `python3 nine/verify_nine.py` from the
package root. Only the standard library is needed. The check independently
expands the source, verifies the source-presentation difference and inverse
row operations, authenticates both whole coefficient tuples, proves each
retained source evaluator exactly equal as a polynomial, rebuilds all16
circuits, and replays480 actual-tuple modular assignments across both domains
and certificate forms. It also checks43,945 two-block cases, 540 calibration
identities, the Pell defects, CRT transport, and finalizer completeness.
`generated/VALIDATION.json` records exact totals. Finite checks validate
implementation and mathematical data; they do not replace the universal
proof and its explicit inherited semantic dependencies.

The search that found the finite layout is not a proof dependency. Operation
counts concern the actual delivered live DAG, not a hand count, a dense
expanded polynomial, or the larger degree-certificate circuit. Source power
evaluation reuses a known sum e=i+j when both B^i,B^j are already available;
otherwise it uses binary squaring. Every resulting multiplication is charged.

## Appendix: the three native-tuple comparison circuits

These retain the packet52 matched source and tuple, not the original31 pair.
The shifted source has 136 weighted records and the certificate isolates
them against the 528 padded quadratic monomials. All use W=174 and padding
position p=81. Their respective Dcode degrees are 4728,4914,7516, with
leading coefficient2 and Kcode=Dmax+348. Thus Ecode=5252,5438,8040.

Use M=2^1182955, a=4096M=2^1182967, c=2^8872242, and replace the primary
source polynomial Gs by (B^81+g)^2 Dcode(B), retaining Jcode=2Gs+Targets.
The positive leading coefficient gives Dcode(B)>B^Dmax>0. On
g<4bB^174, B^81+g<5bB^174, so 2Gs<Z/32 by the same geometric estimate,
where Z=B^(Kcode+1). The target maximum is Kcode-186, so target and mask
bounds have ample slack. In particular Scode+Tcode<B^Ecode.

The low mask recovers nonnegative digits z_i, and the padded word is
B^81+sum z_i B^w_i. Its coefficient bound is
M(1+sum z_i)^2<B/4, so the same sparse-borrow proof recovers the shifted
source. The zero vector is excluded by shifted residual5=1, guaranteeing
g>0 in completeness. No other source premise changes.

Put Hpop=Ecode+W+23. Here Hpop is odd in each comparison and the odd
base exponent permits L=bB^Ecode and N=c B^((Hpop-15)/2), without the
extra factors2 or b used by the primary even-parameter layout. Indeed

    u+pop(Tcode)+1=Hpop*v-30k-21
                        =2[(15*kappa-21)/2+((Hpop-15)/2)*v].

All ratio, normalized-margin, and finalizer steps are identical to the
primary proof. The exact-degree formula remains
188 deg(R)+400 deg(N)+8W+236, giving the three comparison degrees recorded
above. The shared homogeneous source evaluator for the shifted and regular
layouts is exactly proved equal to its explicit 136-term polynomial by the
verifier, not merely sampled. Its factorial correction doubles the diagonal
terms of the homogeneously evaluated source; mixed terms are unchanged.

