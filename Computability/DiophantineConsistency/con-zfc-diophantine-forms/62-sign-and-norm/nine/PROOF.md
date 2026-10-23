# A compact nine-positive equation of degree 1,834,516 in 453 operations

## Theorem and scope

Let F be the integer polynomial defined by
`generated/split_116_positive_global.json`, with the literal fixed leaves
materialized in `fixed/` and bound by `fixed/BINDING.json`. Its nine inputs,
in order, are b,g,h,s,w,C,i,j,n, all strictly positive integers. Its exact
total degree is 1,834,516 and its evaluator has 453 live binary additions,
subtractions and multiplications. Every intermediate register is an
abbreviation, and all exponentiations in the specification have fixed
integer exponents.

Using the identified ordinary native compiler, its compact whole-tuple
adapter, K215/refutation calibration, and Jones numerical ratio theorem,
ZFC proves that F has a positive zero if and only if a finite ZFC refutation
exists. Consequently ZFC proves that F has no positive zero if and only if
Con(ZFC). Neither consistency nor inconsistency is assumed.

The new reductions are proved below. This result supplies ordinary
mathematics formalizable in ZFC and reproducible finite arithmetic data. It
does not provide a new end-to-end Lean/Rocq certificate or an exported
object-language ZFC derivation. The inherited compiler and ratio theorems
remain named dependencies. This is a local improvement over the inspected
repository revision beb0192cb8dc36f78c369c080f2adfbc1887a486, not a global
minimum or a claimed major breakthrough.

## 1. A coherent smaller source

The parent is exactly the 31-positive-coordinate, 22-row, 60-operation
system in `data/parent_system60.json`. It is the package31 shifted transport
presentation used with the whole compact package44 tuple by package52.
Its four coefficient ports are beta,K0,MC,MF, with aliases K0=K and
MF=MF_source. The complete fixed tuple is supplied in `coefficients/`:

* beta has 590069 bits;
* K0 has 592884 bits;
* MC has 590069 bits;
* MF has 590070 bits and is already shifted by B_native-1.

Together the four uncompressed unsigned integer encodings occupy 295388
bytes. Their actual raw hashes agree with package52's binding, retained in
`upstream/COMPACT_BINDING.json`. The finite native compiler builder and
literal K215 transitions are included. `verify.py` reconstructs all four
whole integers, checks all 66062 native basis identities, and checks the
explicit rank controller. The unbounded adapter proof is retained in
`upstream/NATIVE_TUPLE_PROOF.md` and
`upstream/NATIVE_MATCHING_PROOF.md`.

The old package59 split source is *not* rebound without changing its row.
An exact symbolic comparison gives

    r15_new = r15_old - beta*J,

and leaves all other rows identical. This is the justified transport change
z_old=z+1. Its completeness follows from the inherited source zero bounds
z_old>=2, as proved for the shifted 60-operation source. An arbitrary
positive-coordinate substitution by itself would not prove completeness.
The exact comparison is checked with all four ports symbolic.

Apply the invertible row changes

    rho14=r14+r2,   rho15=r15+r3,

leaving other rows unchanged. Their inverses subtract rho2 and rho3, so the
positive common zero set is unchanged. The resulting source has 89 weighted
records, with 7 constant, 39 linear and 43 quadratic records.

## 2. Exact sparse coefficient extraction

In the original 31-variable order use weights

    1,7,61,36,16,85,20,67,43,11,34,13,96,80,29,50,
    2,109,110,112,116,91,53,55,27,101,92,9,107,37,60.

The new row order and corresponding target exponents are

    rows: 2,15,8,17,13,18,12,20,21,4,22,9,11,19,1,6,10,16,3,14,7,5;
    q:    28,124,325,423,598,658,775,904,941,955,1027,1236,1245,
          1313,1323,1530,1571,1584,1637,1787,2014,2036.

Let U_y(T)=sum y_i T^w_i. For a monomial y^alpha of degree d in rho_j,
let e(alpha)=sum alpha_i*w_i. Its weighted coefficient is twice its
ordinary coefficient for d=0,1 and the ordinary coefficient times
product alpha_i! for d=2. Put

    D_d(T)=sum_{j, degree(alpha)=d} c_(j,alpha) T^(q_j-e(alpha)),
    G(T,y)=D_2(T) U_y(T)^2+D_1(T) U_y(T)+D_0(T).

The exact finite certificate in `data/split_code.json` and
`data/split_kernels.json` proves

    [T^q_j] G(T,y) = 2 rho_j(y),  for j=1,...,22.

Indeed, for each degree separately, each supported monomial label is unique
against all monomials of that degree. Every source/expansion interaction
hits a selected target only when it is its own row and monomial. The 22544
interactions include exactly 89 intended contributions. In U_y^2 a square
has multiplicity one and a cross term has multiplicity two; the chosen
weighting therefore recovers twice every coefficient. This proves an
identity with arbitrary witnesses and arbitrary coefficient ports, not a
numerical sample.

The kernel degrees are

    deg D0=1571,  deg D1=1934,  deg D2=1836,
    W=max(w_i)=116,  H=max_d(deg D_d+dW)=2068.

The leading coefficient of D2 is exactly +1. The largest target is 2036.
The certificate has no negative kernel exponent. The target search is not
a proof dependency; the explicit certificate and its checker suffice.

## 3. Coefficient bound, positivity, and source words

Replace native port powers in each weighted coefficient by the strict
corresponding bit bounds and sum absolute values. The maximum resulting
majorant is exactly 2^1182954, and every maximal coefficient involves a
native port whose bound is strict. Hence all actual weighted coefficients
have absolute value strictly below

    M=2^1182954.

This is sharper by one binary exponent than blindly applying bit_length
to a majorant which is already a power of two. Set

    kappa=1182966,  a=2^kappa=4096M,  B=a b^2,
    ell=sum_i B^w_i,  U_s=ell+g,
    G_s=(D2(B)U_s+D1(B))U_s+D0(B),
    Targ=sum_j B^q_j,  N0=B^117,  Z=B^2069,
    Mask=N0-1-(b-1)ell,
    Jcode=2G_s+Targ,
    Scode=g+N0*Jcode,
    Tcode=Mask+N0*(B-2)*Targ,
    Gcap=32 b B^116.

All these exponents are fixed numerals. For every b,g>=1,
U_s>=B^116 and D2(B)>B^1836/2. The potentially negative contributions,
relative to B^1836 U_s^2, have bounds

    |D1 U_s|/(B^1836 U_s^2) < 2M/B^18 < 1/8,
    |D0|/(B^1836 U_s^2) < 2M/B^497 < 1/8.

Therefore G_s>0 unconditionally. Also 0<=Mask<N0, so Scode,Tcode are
nonnegative before recovering binary bases or any bound on g.

On the full ratio soundness range g<4bB^116, one has U_s<6bB^116 and

    2G_s/Z < 86Mb^2/(B-1) < 1/32,
    Targ < Z/64,   (B-2)Targ < Z/64.

The kernel-height estimate is H=2068; the target estimate uses 2036+1<2069.
Also g<N0, because 4b<B. Combining the strict bounds gives

    Scode+Tcode < N0 Z = B^2186.

When b is a power of two, the low mask forces
g=sum z_i B^w_i with 0<=z_i<b. The shifted word U_s then represents
y_i=z_i+1>0. Every coefficient of the split convolution has absolute value
at most M[(sum y_i)^2+sum y_i+1] <=993Mb^2 < B/4. The inherited sparse
signed-borrow padding lemma therefore gives

    Scode AND Tcode=0
       iff g encodes a positive common zero of the compact source.

Its hypotheses, coefficient bounds, target identities, and unconditional
positivity were just established for the changed tuple and layout. See the
complete inherited sparse argument in `upstream/FROZEN_NINE_PROOF.md`;
only its numeric code parameters and parent binding are replaced here.

Conversely a positive source zero gives such a word for every sufficiently
large binary b, and g<bB^116. It gives g>0 because the all-one source tuple
has r5=1. Thus 32g<Gcap, the required completeness margin, holds.

## 4. Exact two-block calibration

Put

    L=bB^2186,
    R=L(Scode+Tcode+1)-Scode-1,
    c0=2^8872234,    N=c0 B^1155.

For every positive outer assignment,
R=(L-1)Scode+L*Tcode+L-1>=L-1>=8, and b<=R,N with N>=8.
On the bounded branch Scode+Tcode<L, including b=1.

If b=2^k, B=2^v and L=2^u, then

    v=1182966+2k,   u=k+2186v,
    R=(Scode+Tcode)L+(L-1-Scode).

The two blocks do not overlap. Writing pop for binary population count and
tau=pop(Scode)+pop(Tcode)-pop(Scode+Tcode), one obtains

    pop(R)=u+pop(Tcode)-tau.

The carry defect tau is nonnegative and vanishes exactly when Scode and
Tcode are binary-disjoint. The low mask contributes 117v-31k bits, and the
22 disjoint high digits B-2 contribute 22v-22 bits. Consequently

    u+pop(Tcode)=2325v-30k-22
                =2(8872234+1155v)=2 log_2 N.

The exact equality uses 15*1182966-22=2*8872234. Legendre's formula
v_2(binomial(2R,R))=pop(R) gives

    N^2 divides binomial(2R,R) iff Scode AND Tcode=0.

The case k=0 is included in the identity. It cannot give a final zero:
then the low mask is N0-1 and 0<g<4B^116<N0, so g AND Mask=g>0.

## 5. The unchanged free-coordinate finalizer

All inputs b,g,h,s,w,C,i,j,n are positive; write j0=j-1>=0. Define

    U=N^2 w,  Y=N^2 s,  M0=RY,
    P=2M0^2 U,  K=R+1+h(P-1),  A=M0(U+1),
    B1=2R+1,  W1=bw,  J=4A-5,
    Q=3W1 C-2(W1^2-1),  D=(A^2-1)C^2+1,
    k0=iJC,  E=k0DC,  F=(A^2-1)E^2+1,
    G=A+F(CD+1-A),  H=C+F(B1+j0 C),
    I=(G^2-1)H^2+1,  a0=(P^2-1)K^2+1,  a1=DFI,
    t=bB^116,  m=K^2(4t-g)-16t(C-KY)^2,
    V0=PK,  Tpair=k0(8D^2-4D-1),  V1=Tpair GH,
    Omega=Jm,  E0=J(n+W1^2)+Q,
    Theta=E0-Omega(V0+V1).

The final equation is the ordinary integer polynomial

    [Theta^2-Omega^2(a0+64a1)]^2 - 256 Omega^4 a0 a1 = 0.

The full finalizer proof is retained verbatim, including its numeric
interface, in `upstream/FREE_COORDINATE_PROOF.md`, Sections 3 and 4. Its
hypotheses depend on R,N>=8, b<=R,N, nonnegative Scode,Tcode and the two
source bounds 8g<Gcap and 32g<Gcap; all were established above. Its other
register definitions are unchanged. For clarity the key steps follow.

For every free C>=1 the strict majorants are

    V0^2-a0=K^2-1>0,
    Tpair^2-64DF=(8D+1)k0^2-64D>0,
    Delta1=V1^2-64a1
      =[(8D+1)k0^2-64D](GH)^2+64DF(H^2-1)>0.

Also E0=Jn+(J-2)W1^2+3W1C+2>0. A norm zero with m=0 would be E0^4>0,
which is impossible. Otherwise the four real norm factors give signed roots
r0^2=a0, r1^2=64a1 and

    n+W1^2+Q/J=m(V0+V1+r0+r1).

The left side and the parenthesis are positive, so m>0 before integrality
is invoked. This gives |C-KY|<K/2 and the old carrier bound
C>2R+1+W1. With that bound a1>a0, so the rational sum r0+r1 is nonzero.
The identity 2(r0+r1)r0=(r0+r1)^2+a0-64a1 proves both roots rational,
hence integral; also r1/8 is integral. The factor equation gives J|Q.
The exact CRT coordinate H=C+F(B1+j0C), with j0>=0, meets the Jones ratio
interface. Its soundness yields binary b, the source range g<4bB^116, and
the binomial divisibility. The source recovery above completes soundness.

Conversely, a positive compact-source zero supplies the outer code and
the Jones ratio witnesses. The inherited exact CRT transport produces
j0>=0, hence positive j. Using positive roots and the positive integer
margin m>=1, choose

    n=m(V0+V1+r0+r1)-W1^2-Q/J.

The bound W1^2+Q/J<2D<V1 proves that this integer is positive. One real
factor then vanishes. This proves completeness without an unsupported
cofinality claim about the quotient j or about the norm coordinate n.

## 6. Exact degree and arithmetic size

The changed source heads have

    deg Scode=4370,  deg Tcode=4308,
    r=deg R=8743,  q=deg N=2310.

The positive leading coefficients are inherited from the +1 head of D2,
the positive offset word, L, and N. Resolve the final cancellation by

    Theta^2-Omega^2(a0+64a1)
      =E0^2-2E0*Omega*(V0+V1)
       +Omega^2[(K^2-1)+Delta1+2V0V1].

The exact identity for Delta1 is checked symbolically. The separate degree
certificate has no unresolved positive-degree cancellation and a nonzero
positive diagonal leading coefficient. The diagonal reaches the ordinary
multivariate upper bound. Thus the degree is exactly

    104r+400q+8W+316 = 1,834,516.

The straightforward adapted Horner circuit has 467 operations. Replacing
its 102 pure B-power multiplication gates by the supplied global chain of
88 gates preserves every required power and every other arithmetic node.
Each chain row is simply e=a+b, certifying B^e=B^a B^b. The checker compares
the full circuits exactly after normalizing these power identities. This
gives 453 operations, including scalar multiplication and every fixed
power multiplication; constants are leaves and reuse is free.

The natural-domain companion substitutes each positive input by that
natural input plus one. It has degree 1,834,516 in nine nonnegative inputs
and 460 operations. No unrestricted-integer nine-variable claim is made.

Relative to package59's 1,910,404/473 point, the new positive form saves
75,888 degrees and 20 operations, while replacing the old 533099-byte
native tuple by the coherent 295388-byte compact tuple. These are separate
complexity measures; the fixed leaves are still large, and circuit operation
count is not bit complexity. The source-degree search and shared addition
chain are finite optimizations, not new universal variable-count theorems.

## 7. Reproducibility and remaining research

Run `python3 reproduce.py` from this directory. It regenerates the source,
all literal circuits, both global power rewrites and the fixed leaves, then
verifies the exact source identities, coefficient recipes, degree and
power-chain certificates. The native adapter is independently regenerated
from the literal machine transitions. Small modular and binary-block
fixtures are explicitly labeled finite checks, not semantic proofs.

Further work should seek a numerical Diophantine interface for the direct
oddness of binomial(Scode+Tcode,Scode). Kummer's carry interpretation would
then avoid the present two-block R and large N threshold; a suitably small
polynomial representation has not been constructed here. Optimizing source
coordinate transformations before choosing weights may give more than
target reordering alone. Finally, the complete native source-to-refutation
bridge and this particular circuit should be kernel formalized before it
replaces the repository's independently certified endpoint.
