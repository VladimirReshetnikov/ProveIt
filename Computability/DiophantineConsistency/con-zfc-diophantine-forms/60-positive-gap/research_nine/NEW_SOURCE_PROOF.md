# Positive source coordinates and the 86-record nine-variable equation

This note proves the new source and packing steps. The numerical Jones ratio
interface and the positivity-first final norm are inherited, unchanged, from
ProveIt package 59, `nine_free_adjunct/PROOF.md`, at commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. The source is the original,
unshifted transport convention reconstructed exactly from that package's
split kernels. Its fifteenth row differs from the published package-31
`quartic31_system60.json` by +beta*J; that coordinate convention must be
identified in the semantic adapter, not silently conflated.

## 1. A positive coordinate change removes two records

Write k=eta+zeta. Among the original 22 quadratic rows, the relevant rows are

    r4 = a-E-sN,
    r5 = E-(a-E)X,
    r6 = c-eta-k(a-E),
    r7 = P-k-E(c-eta),
    r8 = tau^2-P^2+kP-1.

No other row contains P or tau. On every common positive zero, r4 and r6
give a-E=sN>0 and c-eta=k(a-E)>0. Therefore

    p=P-k=E(c-eta)>0.

The eighth row says tau^2=p^2+kp+1>p^2, so the positive integer

    t=tau-p

is strictly positive. Conversely, put

    P=p+eta+zeta, tau=p+t.

For positive p,t these old variables are positive, and exact substitution
turns r7,r8 into

    p-Ec+eta E=0,
    t^2+2pt-eta p-zeta p-1=0.

The first has three records instead of five; the second retains five.
These maps are inverse on the positive common zero sets. All other rows
are unchanged. This is an exact source equivalence, not a cofinal-family
restriction. The active square P^2 is replaced by the active pair pt.

## 2. A square coordinate removes one further record

Use the pre-existing invertible row operations rho14=r14+r2 and
rho15=r15+r3. If q=beta J+1, the first source row is L=q^2-1. Replace L
by S-1, where the new variable S is positive. The first row now forces
S=q^2. Since beta,J>=1, q>=2 and hence S-1>0 on every new zero.
Thus this substitution is also a bijection on positive common zero sets.
The changed rows have the following weighted-record counts:

    row1: 3 -> 4; row2: 5 -> 3; row14: 10 -> 10.

The cancellation in row14 is exact: substituting L=S-1 changes -F L to
-F S+F, cancelling the original -F; -alpha L contributes +alpha.
The 87 records of Section 1 become 86. No quadratic record changes in
this second substitution, including its coefficient. There are 7 constant,
36 linear and 43 quadratic records, representing 39 distinct quadratic
monomials. The two coordinate changes commute.

## 3. Literal source and finite coding certificate

The complete weighted source is `candidate/data/parent_source.json`.
Its records use the original variable order, with index 11 now t, index18
now p, and index24 now S (indices are zero-based). For degrees 0 and 1 a
record coefficient is twice its source coefficient. For degree 2 it is
the source coefficient times the product of the factorials of its variable
multiplicities. This is exactly the coefficient normalization needed for
the identity below.

The 31 weights, 22 row targets and three kernels are literal data in
`candidate/data/split_code.json` and `split_kernels.json`. Their finite
properties are:

    W=100, degree(D0)=1545, degree(D1)=1920, degree(D2)=1847,
    K=max_d(degree(Dd)+dW)=2047, maximum target=2016,
    leading coefficient of D2=1.

For U_y(T)=sum_i y_i T^w_i, the exhaustive certificate checks all 22,451
record/monomial interactions, and proves exactly

    [T^q_j](D2(T) U_y(T)^2+D1(T) U_y(T)+D0(T)) = 2 rho_j(y).

It checks every possible monomial of the corresponding degree, not merely
the supported source pairs. The weights include zero; this is permitted
and is covered by the low-mask decoder. All kernel exponents are nonnegative
and distinct inside each homogeneous degree. The source search is not a
proof dependency; the finite certificate and checker are sufficient.

## 4. The source inequalities, without a binary-base assumption

For the whole original31 tuple, every weighted coefficient has absolute
value below M=2^2134927. Define the fixed integer

    a=4096M=2^2134939, B=a b^2,
    ell=sum_i B^w_i, U_s=ell+g,
    G_s=D2(B)U_s^2+D1(B)U_s+D0(B),
    T_q=sum_j B^q_j, N0=B^101, Z=B^2048,
    Mask=N0-1-(b-1)ell,
    Jcode=2G_s+T_q,
    Scode=g+N0 Jcode,
    Tcode=Mask+N0(B-2)T_q,
    Gcap=32bB^100.

Here b,g are positive, not yet known to have any binary property. The
distinct kernel exponents and coefficient bound give

    D2(B)>B^1847/2,
    |D1(B)|<2M B^1920, |D0(B)|<2M B^1545.

Since U_s>=B^100, the two negative contributions relative to
B^1847 U_s^2 are below 2M/B^27 and 2M/B^502. Each is below 1/8, so
G_s>B^1847 U_s^2/4>0. Thus Scode,Tcode>=0 unconditionally. The mask has
base-B digits B-b at the 31 selected weights and B-1 elsewhere, and
0<=Mask<N0. There is no circular invocation of a final zero here.

On the exact soundness branch g<4bB^100, we have U_s<6bB^100 and

    |G_s| < 43 M b^2 B^2048/(B-1),
    2G_s/Z < 86 M b^2/(B-1) < 1/32.

Since max q_j=2016, both T_q and (B-2)T_q are below Z/64. Also
g<N0 because 4b<B. It follows that

    Scode+Tcode < N0 Z=B^2149.

All relevant source ranges are proved on the full four-word soundness
range, not just on the narrower completeness range.

## 5. Digit recovery and a new exact valuation calibration

When b=2^k and B=2^v, v=2134939+2k, the low mask recovers precisely

    g=sum_i z_i B^w_i, 0<=z_i<b; y_i=z_i+1.

All coefficients h_t of the source convolution satisfy

    |h_t|<M((sum_i y_i)^2+sum_i y_i+1)<=993Mb^2<B/4.

At a marked target the signed digit of Jcode is 2h_t+1. Incoming binary
borrow is either -1 or 0. Modulo B, this digit avoids the mask B-2 exactly
when h_t=0. Positive h_t gives a digit from 2 up to B/2; negative h_t gives
a digit above B/2; h_t=0 gives 0 or1. This proves, using the exact finite
target identities,

    Scode & Tcode=0 iff g encodes a positive common source zero.

The bounds in Section4 make these finite integer words. Conversely every
positive source zero can be encoded with every sufficiently large binary b;
then 0<g<bB^100 and 32g<Gcap. The all-one tuple is not a new source zero
(indeed the square coordinate S must exceed1), ensuring g>0.

Set

    L=bB^2149,
    R=L(Scode+Tcode+1)-Scode-1,
    c=2^17079501, N=cbB^1128.

For all positive outer assignments, R>=L-1>=8 and b<=R,N. On the bounded
branch Scode+Tcode<L, including b=1. For binary b,B the two nonoverlapping
blocks of R give

    pop(R)=log2(L)+pop(Tcode)-tau,
    tau=pop(Scode)+pop(Tcode)-pop(Scode+Tcode)>=0.

Here tau vanishes exactly when Scode&Tcode=0. Direct mask counting yields

    pop(Tcode)=123v-31k-22,
    log2(L)+pop(Tcode)=2272v-30k-22=2log2(N).

The last identity uses 2*17079501=16*2134939-22. Legendre's formula gives

    N^2 divides binomial(2R,R) iff Scode&Tcode=0.

The boundary b=1 cannot yield a final zero, since its low mask is N0-1 and
the bounded branch has 0<g<N0. No completeness witness is lost.

## 6. The unchanged numerical tail

Insert precisely these R,N,Gcap and tcap=bB^100 into the numerical tail in
the inherited package59 proof. Its nine positive inputs remain

    b,g,h,s,w,C,i,j,n, with internal j0=j-1>=0.

Its normalized margin is m=Kratio^2(4tcap-g)-16tcap(C-Kratio Y)^2.
All tail proofs use only the source interface established above. In
particular the positivity-first norm forces m>0 before applying the Jones
ratio theorem, recovers the free-carrier range, proves both radicands square
and the exact divisibility, and has a positive final witness n in
completeness. There is no change to that proof or any of its coefficients.

The resulting polynomial is the literal, division-free DAG
`candidate/generated/gap_100_positive.json`. The positive-domain statement
is the primary theorem. The natural-domain DAG is the bijective all-inputs
plus-one translation, not an unrestricted-integer statement.

## 7. Exact degree and operation count

On the all-inputs diagonal, deg R=8595 with head2a^4297, and deg N=2257
with head c a^1128. The identical cancellation-resolving norm calculation
gives

    degree F9=104*8595+400*2257+8*100+316=1,797,796,
    diagonal leading coefficient=2^186 a^898488 c^400>0.

The exact degree auditor obtains the same full multivariate upper bound
and the stated nonzero diagonal term, so this is equality, not a naive DAG
degree estimate. The 465-operation positive evaluator has 159 additions,
22 subtractions and284 multiplications. All fixed powers are compiled into
charged multiplication gates, and every gate in the ledger is live.

The degree reduction from package59 is112608 (5.894460%). The operation
count falls by8 (1.691332%). These are concrete but incremental improvements;
they do not establish a global simplest equation or a new universal
variable bound. The new conceptual ingredient is the positive source
coordinate redesign before sparse coding, rather than merely searching a
different layout of an unchanged source.

## 8. Coherent compact-tuple companion

The argument is uniform in the four coefficient ports, once a complete
positive-source semantic adapter and coefficient bounds are supplied. For
the whole compact tuple with bit lengths590069,592884,590069,590070, the
same source recipes give M=2^1182955 and a=2^1182967. The calibration changes
only the fixed threshold coefficient to c=2^9463725, since
2*9463725=16*1182967-22. Degree, gate count, labels and source identities are
unchanged. This companion must be bound to that entire tuple and its
unshifted transport adapter; individual ports must not be mixed.

## Proof boundary

All new steps above are elementary integer polynomial identities,
inequalities, finite coefficient checks and valuation arguments. They
preserve the existing semantic proof dependencies. The complete consistency
statement still imports the native compiler/calibration theorem and the
Jones numerical ratio theorem. Neither this source change nor finite
testing supplies an object-language ZFC derivation or a new end-to-end
Lean/Rocq certificate. No consistency assumption is used.
