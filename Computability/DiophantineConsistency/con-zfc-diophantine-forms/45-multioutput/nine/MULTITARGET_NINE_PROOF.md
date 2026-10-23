# Nine-variable equation from multi-target quadratic carry coding

## Statement and dependencies

The generated positive equation has nine strictly positive integer unknowns,
788 live binary arithmetic operations, and total degree exactly 129875980.
The corresponding nonnegative-integer equation has 791 operations and the same
degree. Neither equation is asserted to have the same property over unrestricted
integers. Every named intermediate below is a polynomial register, not another
quantified unknown.

The equivalence is an ordinary mathematical theorem formalizable in ZFC:
there is no zero in the stated domain if and only if Con(ZFC). This is not a proof
of consistency, a new end-to-end proof-assistant certificate, or a minimum claim.

The imported semantic dependencies are (a) the coherent compiler tuple and the
31-positive-variable quadratic system of package 31 at repository commit
22e75dd6b87b1b199bb08c778d7cf075ae5aae08, whose zero existence is equivalent to a
finite syntactic ZFC refutation; (b) the two arithmetic ratio theorems in
Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean,
`Jones1982.Nine.ratio_sound` and `ratio_complete`. Their relevant numerical
hypotheses are explicitly discharged below. The new source coding is proved
here directly; it does not silently instantiate a Jones theorem whose statement
fixes the old powers 5^j. The standard binary-digit/central-binomial identity is
also proved below. Package 31's shifted quadratic system is used as a whole,
not mixed with the older package 30 or 37 polynomial.

## 1. Fixed coefficients and isolated positions

Let r_1,...,r_22 be the residuals of `quartic31_system60.json`, in its displayed
comparison order, after substituting each of its 31 positive coordinates by
z_i+1. The exact source SHA256 is
ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48.
All r_j have degree at most two. The fifth residual at z=0 is 1, so no common
zero has every z_i zero.

Use the 31 weights in `../quartic/B2_CERTIFICATE.json`:

10,35,55,62,105,144,145,159,168,232,245,306,323,325,353,371,374,
382,494,499,525,566,578,610,647,681,685,741,777,783,799.

The 528 sums sum alpha_i w_i with |alpha|<=2 are distinct. This finite fact is
independently checked by enumeration; the Bose--Chowla construction provides a
second explanation but is not necessary as an additional unverified premise.
Put W=799, d=2W+1=1599. Reorder the residuals as 1,2,3,4,6,...,22,5; denote the
reordered rows by p_1,...,p_22. Their target exponents are h_j=j d. Thus
Hmax=35178 and Kcode=Hmax+2W=36776.

Write p_j(z)=sum_alpha p_(j,alpha) z^alpha and define
c_(j,alpha)=(2-|alpha|)! product_i(alpha_i!) p_(j,alpha).
The exact 136 terms, coefficient expressions in the fixed four ports, and
exponents are in `../quartic/QUADRATIC_TARGETS.json`. The coefficient order is
(beta,K0,MC,MF), with the complete package-31 tuple, not independently chosen
ports. Its bit-length bounds are (1064921,1070004,1064921,1064922).

For each coefficient recipe c=sum_t a_t product port_i^e_ti compute
B_c=sum_t |a_t| 2^(sum_i e_ti bitlength(port_i)). The builder checks these finite
integer sums and takes the bit length of their maximum. It is 2134927.
Consequently |c|<M=2^2134927 for every one of the 136 coefficients. This is a
bound on the quadratic records, not the older quartic coefficient bound.
Set the fixed base floor b_floor=2^2134939=4096M. Both are explicit ordinary
integers; the floor is the only additional fixed coefficient beyond the small
collection of quadratic coefficient recipes. No dense Jones enumeration index,
unknown recursively enumerable index, variable exponent, or infinite search
is part of the equation.

## 2. Two-variable source

Initially use epsilon,phi,n>=0 and g,h,s,w,i,j>=1. These are nine coordinates.
Define

b=b_floor+epsilon, B=b^3,
ell=sum_i B^w_i,
Dcode=sum_(j,alpha) c_(j,alpha) B^(h_j-alpha.w),
N0=B^(W+1), N1=4B^(Kcode+1), N=N0 N1,
Mask=N0-1-(b-1)ell,
Targets=sum_(j=1)^22 B^h_j,
Tcode=Mask+(B-2)Targets N0,
Jcode=2(1+g)^2 Dcode+B sum_(k=0)^Kcode B^k,
Scode=g+Jcode N0,
R=(N-1)[(Scode+Tcode+1)N+Tcode+1],
Gcap=32b B^W.

All exponents are fixed positive integers. Because each row's shifted support
lies in [h_j-2W,h_j], these supports are disjoint. Within each row its support
is injective by the 528-sum certificate. Thus every coefficient of Dcode, as a
polynomial in B, has magnitude less than M. The top coefficient, at Hmax, is
2: the fifth original residual was deliberately moved last and has constant
coefficient 1. All remaining terms have smaller exponents. Since B-1>M,

Dcode > 2B^Hmax-M sum_(k<Hmax)B^k > B^Hmax >0,
Dcode < M sum_(k<=Hmax) B^k < M B^(Hmax+1)/(B-1).

These facts hold for every outer assignment, even when g is unbounded. Also
ell<(B^(W+1)-1)/(B-1), because its exponents are a proper subset of
{0,...,W}. Since b-1<B-1, Mask>0. Hence Tcode, Jcode, Scode are positive and
R>=N>=8 and R>=b for every outer assignment. This unconditional positivity is
why the earlier large signed-majorant repairs are no longer necessary.

If g<4b B^W, then 1+g<=4b B^W and g<N0, since 4b<B. The preceding Dcode bound
gives

2(1+g)^2 Dcode < 32M b^2 B^(Kcode+1)/(B-1).

As b>=4096M, 32M b^2<=B/128. Adding the geometric mask shows
0<Jcode<4B^(Kcode+1)=N1. Moreover
(B-2)Targets < B^(Hmax+1), so 0<=Tcode<N0 N1=N.
Thus 0<=Scode,Tcode<N on this bounded-g branch. No polynomial zero or carry
condition is assumed in these bounds.

## 3. Binary carries encode all 22 equations simultaneously

Assume b is a power of two and g<4b B^W. Then B,N0,N1,N are powers of two.
For 0<=S,T<N, write N=2^r. An exact identity is

(N-1)[(S+T+1)N+T+1]
 =(S+T)N^2+(N-1-S)N+(N-1-T).

The lower two blocks lie in [0,N); the high block can have an extra digit but
does not overlap them. Binary digit sums therefore give

popcount(R)=2r+popcount(S+T)-popcount(S)-popcount(T)
           =2r-tau_2(S,T).

Here tau_2 counts binary carries with multiplicity. Legendre's factorial
formula gives v_2(binomial(2R,R))=popcount(R). Therefore

N^2 divides binomial(2R,R) iff tau_2(Scode,Tcode)=0.

By the strict bounds on the two low and high blocks, this is equivalent to
both tau_2(g,Mask)=0 and tau_2(Jcode,(B-2)Targets)=0. A carry out of the low
block already fails the full no-carry test, so no hidden no-overflow
assumption is used.

The base-B digits of Mask are B-b at each allowed weight w_i, and B-1
elsewhere through W. Since b and B are powers of two, the mask condition
is exactly

g=sum_i z_i B^w_i, 0<=z_i<b.

For such g, form C(t)=(1+sum_i z_i t^w_i)^2 and the formal Dcode(t). The
coefficient at h_j in C Dcode is 2p_j(z). Indeed row j matches precisely the
same exponent multiset; a different row k cannot contribute since
|h_j-h_k|>=2W+1 while the difference of two sums of at most two weights has
absolute value at most 2W. This proves simultaneous, not merely individual,
coefficient extraction. It also handles zero and linear monomials through
the factorial factors and the constant term of C.

Every coefficient of C Dcode has magnitude at most
M(1+sum_i z_i)^2<=M(32b)^2<=B/4<B/2.
The degree is at most Kcode. Set a_k=coeff_k(C Dcode)+B/2. Then 0<a_k<B and

Jcode=2 sum_(k=0)^Kcode a_k B^k.

Meanwhile (B-2)Targets=2 sum_j (B/2-1)B^h_j. Divide both operands by 2; this
is just a common binary shift. At each target cell the mask consists of all
low log_2(B)-1 bits. Its disjointness from the digit a_hj, with 0<a_hj<B,
forces a_hj=B/2, equivalently p_j(z)=0. All target cells are distinct and
all nontarget mask cells are zero. Thus

b a power of two, 0<g<4bB^W, N^2|binomial(2R,R)
 implies existence of a common nonnegative zero of p_1,...,p_22.

Conversely, given such a common zero z, choose an arbitrarily large power
of two b>=b_floor with b>max z_i, set epsilon=b-b_floor and
g=sum_i z_i B^w_i. The normalization implies g>0. Furthermore

g <=(b-1)ell < bB^W,

because (b-1)B/(B-1)<b. Both carry conditions hold, hence the central
binomial divisibility holds. In particular 32g<Gcap. This proves exactly
the source contract needed by the ratio bridge.

## 4. The unchanged Jones ratio bridge

Define the following registers using the source R,N,b,g,Gcap and five positive
witnesses h,s,w,i,j plus nonnegative phi:

U=N^2 w, Y=N^2 s, M0=RY, P=2M0^2 U,
K=R+1+h(P-1), A=M0(U+1), B1=2R+1, W1=bw,
C=B1+W1+phi, J=4A-5,
Q=3W1 C-2(W1^2-1),
D=(A^2-1)C^2+1, E=i J D C^2,
F=(A^2-1)E^2+1,
G=A+F(CD+1-A), H=B1+jC,
I=(G^2-1)H^2+1,
a0=(P^2-1)K^2+1, a1=DFI,
u=JF, v=QF+J(H-C),
m=K^2 Gcap-4(C-KY)^2 Gcap-8gK^2.

The cited ratio_sound theorem says: if R,N>=8, b<=R,N, b,Gcap>0,
h,s,w,i,j>0, phi>=0, and a0,a1 are squares, u|v, m>0, then
N^2|binomial(2R,R), b is a power of two, and 8g<Gcap. The source has proved
all numerical hypotheses unconditionally. The last inequality gives exactly
g<4bB^W, so Section 3 applies without circularity.

Conversely ratio_complete says that the same numerical hypotheses together
with the central-binomial divisibility, b a power of two, and 32g<Gcap admit
h,s,w,i,j>0 and phi>=0 satisfying those four conditions. These are precisely
the stronger source bounds obtained in the previous section. No assumption
about the old q=B^(5^(nu+1)) is part of these numerical ratio theorems.

## 5. A cheaper finalizer using strict positive majorants

Every register in this section has its value on an arbitrary outer assignment;
no square or margin assumption is made. R,N,b positive imply P,K,A,C,J,D,E,F,H>1.
Since C>=1 and D=(A^2-1)C^2+1>=A^2, CD+1>A, hence G>1 and I>0.
In particular a0,a1,u are strictly positive.

Set V0=PK and V1=(AC)(AE)(GH). The identities

V0^2-a0=K^2-1>0,
(AC)^2-D=C^2-1>0,
(AE)^2-F=E^2-1>0,
(GH)^2-I=H^2-1>0

prove 0<a0<V0^2 and 0<a1<V1^2. Thus V0,V1 are strict square-root majorants;
no added 1 or sign-repair polynomial is needed.

Also C>W1>0, so Q=3W1 C-2(W1^2-1)>0. Since
H-C=B1+(j-1)C>0 and J,F>1,

0<v/u=Q/J+(H-C)/F<Q+H-C<Q+H-1.

Take Mdiv=Q+H. It is positive and |v/u|<Mdiv-1.
Define

Omega=um,
Theta=u(n+Mdiv)+v-Omega(2Mdiv+V0 V1),
F9=(Theta^2-Omega^2(a0+V0^2 a1))^2
    -4Omega^4 V0^2 a0 a1.

The requested equation is F9=0. If m=0, then Omega=0 and
Theta/u=n+Mdiv+v/u>0, so F9 cannot vanish. Otherwise the usual four-factor
identity shows that Theta/Omega=r0+V0 r1 for some complex roots r_t^2=a_t.
Here a_t>0, so the roots are real. If this rational number is nonzero,
2(Theta/Omega)r0=(Theta/Omega)^2+a0-V0^2 a1 makes both roots rational, hence
integers. If it were zero, then |r1|=|r0|/V0<1, contradicting the positive
integer a1=r1^2. Thus the roots are always integers.

The strict majorants now imply |r_t|<=V_t-1. Consequently
Z=2Mdiv+V0V1+r0+V0r1>=2Mdiv+1>0. The vanishing factor becomes

n+Mdiv+v/u=mZ.

Its left side is positive, forcing m>0. Since the right side and n+Mdiv are
integers, u divides v. Conversely when a0,a1 are squares, u divides v, and
m>0, choose integer roots and set n=mZ-Mdiv-v/u. The displayed bounds give
n>=2, and the corresponding factor vanishes. This proves the finalizer in
both directions and excludes the previously troublesome zero-margin branch.

Combining Sections 3--5 with the imported fixed quadratic compiler proves
F9 has a zero iff there is a finite ZFC refutation. Negation proves the
stated ZFC-provable consistency equivalence.

For nine strictly positive coordinates replace epsilon,phi,n by their
positive coordinates minus 1; g,h,s,w,i,j are already positive. For nine
nonnegative coordinates replace each of g,h,s,w,i,j by its coordinate plus 1.
These are domain bijections. They do not authorize interpreting the equation
over all integers.

## 6. Exact degree, not merely a gate upper bound

Let t=deg N=3(Hmax+3W+2)=112731. On the diagonal where all nine variables
are assigned an indeterminate T, N has leading coefficient 4 and R degree
3t, leading coefficient 16. The geometric mask in Jcode uniquely dominates
its sparse coefficient term, and the Scode N^2 term uniquely dominates R.
These assertions hold for the actual fixed coefficients and for every allowed
specialization of the coherent tuple; no numerical modular coincidence is used.

Degree/leading-coefficient pairs for the tail are:

N: t / 2^2; R:3t /2^4;
U,Y:2t+1 /2^4; P:12t+3 /2^21; K:12t+4 /2^21;
A:7t+2 /2^12; C:3t /2^5; J:7t+2 /2^14;
D:20t+4 /2^34; E:33t+7 /2^58; F:80t+18 /2^140;
G:103t+22 /2^179; H:3t+1 /2^5; I:212t+46 /2^368;
a0:48t+14 /2^84; a1:312t+68 /2^542;
u:87t+20 /2^154; m:28t+3W+11 /(-2^57);
Omega:115t+3W+31 /(-2^211);
V0:24t+7 /2^42; V1:156t+34 /2^271.

The important leading cancellation V1^2-a1 is resolved by the exact identity

Delta=(C^2-1)(AE)^2(GH)^2
      +D(E^2-1)(GH)^2+DF(H^2-1).

The first two summands both have degree 298t+64 and leading coefficient
2^518; their positive sum has leading coefficient 2^519. The third has
lower degree. Set E0=u(n+Mdiv)+v-2Omega Mdiv. Then exactly

Theta^2-Omega^2(a0+V0^2 a1)
 =E0^2-2E0 Omega V0V1+Omega^2 V0^2 Delta-Omega^2 a0.

The third term uniquely dominates, with degree 576t+6W+140 and leading
coefficient 2^1025. The final subtracted term in F9 has lower degree.
Consequently

deg F9=1152t+12W+280=162444W+83224=129875980,

with nonzero diagonal leading coefficient 2^2050. The displayed degree
bounds also hold for full multivariate total degree, so the diagonal lower
bound proves equality. The separate generated degree-certificate circuit
uses these identities exactly and has no unresolved leading cancellation.

## 7. Reproducibility and limitations

`build_multitarget_nine.py` reads only mathematical JSON data; it does not
execute upstream programs. It builds the primary and cancellation-resolved
circuits, including every fixed power as additions/multiplications. It charges
all live binary additions, subtractions, scalar multiplications and squarings.
`verify_multitarget_nine.py` checks the 528 pair sums, both domain translations,
180 prime-field circuit/certificate replays, 15 additional replays with the
actual port tuple modulo primes, reconstruction and hash verification of all
17 materialized fixed coefficient payloads, exact symbolic degree leaders,
128 finalizer completeness fixtures, 980 zero-margin exclusions, and 352
independent target extractions. The independent parent/target checks are in
`../quartic/verify_quadratic_targets.py`.

The fixed coefficient bound is regenerated from the 136 actual symbolic
recipes and the complete tuple's verified bit-lengths. These finite audits
check implementation and source transcription. They do not decide consistency,
search unboundedly for a zero, or substitute for the mathematical proof above.
The inherited compiler contract and ratio theorems are explicitly identified
rather than represented as newly rebuilt kernel certificates.
