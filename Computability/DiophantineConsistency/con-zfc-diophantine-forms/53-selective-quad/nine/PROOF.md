# Nine natural or positive unknowns with a parity-calibrated carry block

## 0. Result and exact scope

The primary equation is `F9=0`, defined by the division-free circuit
`generated/calibrated_natural.json` on nine nonnegative integers. Its bijective
positive-coordinate translate is `generated/calibrated_positive.json`. Both
have exact total degree **7,344,328**. The positive circuit has **738** live
binary arithmetic operations: 211 additions, 26 subtractions and 501
multiplications; the natural circuit has 744. Every named register below is a
polynomial abbreviation, not an additional unknown. All powers have fixed
integer exponents; all leaves are explicit fixed integers or one of nine inputs.

Using the explicitly identified inherited compiler and Jones ratio theorems,
the proof below is ordinary mathematics formalizable in ZFC and establishes

    a zero in the stated domain exists iff a finite syntactic ZFC refutation exists.

Taking negations gives absence of zeros iff Con(ZFC). This is neither a proof
of consistency nor a new end-to-end kernel-checked formalization. There is no
nine-variable assertion over unrestricted integers, no global minimum claim,
and no claim that finite regression checks prove the universal theorem.

The independently compiled conservative three-block version has degree
12,023,320 and 734 positive operations. A two-block version that instead
restricts b=2(epsilon+1)^2 has degree 14,687,132 and 740 positive operations.
The primary form therefore improves degree at a cost of four operations over
the conservative version. The package45 repository comparator has degree
129,875,980 and 788 positive operations; it uses a different shifted transport
normalization, so the comparison is of complete independently bound equations,
not an assertion that the source polynomials are identical.

## 1. Coherent source and explicit constants

Let p_1,...,p_22 be the residuals of `upstream/upstream_parent_quartic31.json`
after replacing all 31 positive variables by x_i+1. Its SHA256 is
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.
This is the **original package31 positive-transport source**. In particular,
row15 is not replaced by the package45 transport variant. Package45 subtracts
beta*(x_J+1) from that shifted row; the attached selective checker confirms the
precise difference but the builder does not use its coefficient recipes.

The original source's zero-existence equivalence is the inherited package31
compiler interface, with the whole 121-by-8801, 943-tile tuple. The four fixed
ports are beta, K0=K, MC, MF=MF_source, and MF_source is already shifted.
`COEFFICIENT_BINDING.json`, `coefficients/original_binding.json`, and four
compressed **little-endian** integer payloads bind these ports together. Their
bit lengths are 1064921, 1070004, 1064921 and 1064922. The source/compiler
contract is explained in the included `upstream/SIGNED10_PROOF.md` and the complete
tuple adapter proof `upstream/COEFFICIENT_PROOF.md`; the present
work imports that contract, not a newly formalized universal-machine proof.

For a source monomial x^alpha define

    c_(j,alpha)=(2-|alpha|)! (product_i alpha_i!) [x^alpha]p_j(x).

There are 136 nonzero displayed terms. Their 26 distinct coefficient recipes
(including literal-only recipes) occur in each circuit's metadata. The builder
reconstructs them by exact binomial expansion of the original source, never by
executing upstream code or using a guessed recursively enumerable index. For
each recipe sum a_e product port_i^e_i, its magnitude is strictly bounded by
sum |a_e| 2^(sum e_i bitlength(port_i)). The largest such integer bound has
bit length 2134927. Put

    M=2^2134927, kappa=2134940, a=2^kappa=8192M,
    c=2^(15kappa/2-10)=2^16012040.

Thus every |c_(j,alpha)|<M. The integer kappa is even. The coefficients a and c
are explicit ordinary integers defined by fixed exponents; neither is an
unknown nor a variable-exponent operation. The port payloads and these fixed
recipes are sufficient to reconstruct every coefficient without network access.

## 2. Selective extraction, rather than a full Sidon code

The fixed code is `upstream/code_v1.json`, SHA256
`53cfdccbb252fd3f6ebe87ae0bb9dad8b2fdfc8c6168f668029add30ed339e25`.
The positive input weights, in the parent's variable order, are

    9,25,23,139,35,151,168,21,91,181,94,52,150,180,7,135,
    38,88,183,106,178,136,20,138,8,64,105,154,37,137,120.

Reorder the residuals by

    16,2,9,14,21,7,15,22,13,3,19,20,1,10,17,8,4,6,11,18,12,5,

and give them the corresponding targets

    70,86,451,685,1050,1296,1530,1874,2212,2358,2696,2780,
    2792,3157,3290,3634,3929,4238,4384,4527,4865,5190.

Write W=183, Qcode=5190, Kcode=Qcode+2W=5556 and Ecode=Kcode+W+2=5741.
Let e(alpha)=sum alpha_i w_i, and q_j be the target assigned to residual j.
The exhaustive finite certificate proves that, for every source-supported
alpha and every beta of degree at most two,

    q_j-e(alpha)+e(beta)=q_l iff j=l and alpha=beta.

All q_j-e(alpha) are nonnegative and mutually distinct. This is weaker than
requiring every one of the 528 padded pair sums to differ: only the 71 used
pairs must be isolated. The checker enumerates all 136*528=71808 interactions;
exactly the intended 136 land at targets. Repeated reversed exponents would
violate the same condition, so coefficient bounds suffer no collision factor.

Define the formal polynomial

    Dcode(t)=sum_(j,alpha) c_(j,alpha) t^(q_j-e(alpha)).

For C_x(t)=(1+sum_i x_i t^w_i)^2, factorial cancellation and the certificate give

    [t^q_j](C_x Dcode)=2p_j(x).

The leading coefficient of Dcode is 2 at exponent 5190 because residual5 is
last and its constant coefficient is 1. Every other coefficient has magnitude
less than M. Therefore, whenever B-1>M,

    B^5190 < Dcode(B) < M B^5191/(B-1).

This establishes positivity on every outer assignment, not just solutions.

## 3. Sparse +1 target padding and unconditional source bounds

Use natural coordinates

    epsilon,g0,h0,s0,w0,phi,i0,j0,n >= 0,

and set g=g0+1, h=h0+1, s=s0+1, w=w0+1, i=i0+1, j=j0+1. Define

    b=epsilon+2, B=a b^2,
    ell=sum_i B^w_i, A_targets=sum_j B^q_j,
    N0=B^184, Z=B^5557, L=2b B^5741,
    Mcode=N0-1-(b-1)ell,
    Jcode=2(1+g)^2 Dcode(B)+A_targets,
    Scode=g+N0 Jcode,
    Tcode=Mcode+N0(B-2)A_targets,
    R=L^2+(Scode+Tcode)L+L-1-Scode,
    N=c B^2966, Gcap=32b B^183.

Here L is the binary-block size, while N is the **different** square-root
threshold supplied to Jones's ratio theorem. Confusing them changes the
polynomial and invalidates the argument.

For every natural assignment, b>=2 and B>a, Dcode(B)>0, Jcode>0 and Scode>0.
The base-B digits of Mcode are B-b at each weight and B-1 elsewhere through W;
thus 0<=Mcode<N0 and Tcode>=0. Rewriting

    R=L^2+(L-1)Scode+L Tcode+L-1

proves R>=8 and b<=R unconditionally. Also N=c B^2966>=8 and N>=b, while
Gcap>0. No binary-base assumption or upper bound on g was used here.

Now suppose g<4b B^183. Integrality gives 1+g<=4b B^183 and g<N0. Hence

    2(1+g)^2Dcode(B)
      < 32M b^2 B^5557/(B-1)
      = B B^5557/[256(B-1)] < Z/128.

Also A_targets< B^5191/(B-1)<=Z/(B-1)<Z/128, so 0<Jcode<Z/64<Z.
Moreover (B-2)A_targets<B^5191<=Z. As Jcode and the latter quantity are
integers, their strict bounds, together with g,Mcode<N0, give

    0<=Scode,Tcode<N0 Z=B^5741,
    Scode+Tcode<2B^5741<L.

These prebinary bounds justify all subsequent block and carry identities.

Assume next that b is a power of two. Then B is a power of two. The low-mask
condition g & Mcode=0 is equivalent to

    g=sum_i x_i B^w_i with 0<=x_i<b.

For such x let h_r=[t^r](C_x Dcode).
Then

    |h_t|<M(1+sum x_i)^2 <1024M b^2=B/8,
    Jcode=sum_(t=0)^5556 (2h_t+delta_t)B^t,

where delta_t is 1 at a marked target and 0 elsewhere. This sparse +1
background replaces the dense B times geometric sum.

To normalize these signed digits, start with incoming borrow c_-1=0 and set
c_t=floor((2h_t+delta_t+c_(t-1))/B). Inductively c_t belongs to {-1,0}; its
normalized digit is (2h_t+delta_t+c_(t-1)) mod B. At a target delta_t=1:

- If h_t=0, the digit is 0 or 1, so it avoids the mask B-2.
- If h_t>0, it lies between 2 and B/2, so a masked bit is present.
- If h_t<0, its normalized value lies strictly above B/2, again containing a
  masked bit.

Consequently Jcode & ((B-2)A_targets)=0 iff every target h_qj=0, which by
Section2 is equivalent to every p_j(x)=0. Since Jcode>0 and Jcode<Z, this is
ordinary finite binary disjointness; no negative-integer bit convention occurs.
Combining the low/high blocks proves

    Scode & Tcode=0 iff g codes a common zero of all 22 residuals.

## 4. New parity calibration of the two-block threshold

For nonnegative S,T with S+T<L=2^u, put

    X=L^2+(S+T)L+(L-1-S).

These are nonoverlapping binary blocks: a top bit, the word S+T, and the u-bit
complement of S. Thus, writing pop for binary digit sum,

    pop(X)=1+pop(S+T)+u-pop(S)
          =u+pop(T)+1-[pop(S)+pop(T)-pop(S+T)].

The bracket is nonnegative and vanishes exactly when S&T=0. Legendre's
factorial valuation formula gives v_2(binomial(2X,X))=pop(X). Therefore

    2^(u+pop(T)+1) divides binomial(2X,X) iff S&T=0.

For our unchanged sparse mask, put b=2^k and B=2^v, so v=kappa+2k. Its low
part has (W+1)v-31k set bits, and its 22 high target digits each have v-1.
Hence

    pop(Tcode)=206v-31k-22.

The new idea is to calibrate **the block length** by the already existing b:
L=2b B^5741, rather than force b into a quadratic subfamily or introduce
another unknown. Consequently u=1+k+5741v and

    u+pop(Tcode)+1=5947v-30k-20
                    =5947kappa+11864k-20.

Since kappa is even, this is exactly twice

    log_2(N)=(15kappa/2-10)+2966v.

Therefore N^2 is exactly the tested power of two. The source contract is

    b power of two, g<4b B^183, N^2|binomial(2R,R)
      implies a common nonnegative zero of the source residuals.

Conversely, given such a source zero x, choose any sufficiently large power
of two b>max_i x_i, and let epsilon=b-2. The source is not the zero vector
because p_5(0)=1, so g=sum x_i B^w_i is positive. Also

    g <=(b-1)ell < b B^183,

since B>b. Thus 32g<Gcap, both mask conditions hold, and N^2 divides the
central binomial coefficient. **Every sufficiently large power of two is
allowed.** No sparse-base cofinality assumption is hidden in the primary form.

## 5. Jones's unchanged arithmetic ratio interface

Define the following polynomial registers:

    U=N^2 w, Y=N^2 s, M0=RY, P=2M0^2 U,
    K=R+1+h(P-1), A=M0(U+1), B1=2R+1, W1=bw,
    C=B1+W1+phi, J=4A-5,
    Q=3W1 C-2(W1^2-1),
    D=(A^2-1)C^2+1, E=iJDC^2, F=(A^2-1)E^2+1,
    G=A+F(CD+1-A), H=B1+jC, I=(G^2-1)H^2+1,
    a0=(P^2-1)K^2+1, a1=64DFI,
    u=JF, v=QF+J(H-C),
    mu=K^2 Gcap-4(C-KY)^2Gcap-8gK^2.

The inherited `Jones1982.Nine.ratio_sound` and `ratio_complete` are in the
included `upstream/NineRatio.lean`. Their hypotheses are R,N>=8, 0<b<=R,N,
Gcap>0, h,s,w,i,j>0 and phi>=0. These hold unconditionally by Section3 and the
domain shifts. Their four conditions are a0 square, DFI square, u|v, mu>0.
Multiplication by 64 does not change whether an integer is a square.

Soundness supplies b a power of two, N^2|binomial(2R,R), and 8g<Gcap, giving
the bounded-g branch needed in Sections3–4. Completeness applies to the source
construction with its stronger 32g<Gcap, and produces the six arithmetic
witnesses h,s,w,phi,i,j. These ratio theorems do not specify the old giant
Jones radix, the number of source target cells, or L=N. Only their displayed
numerical hypotheses are imported; all source replacements are proved here.

## 6. Sharp near-square majorant and one-polynomial finalizer

Every claim in this paragraph holds on every outer assignment. A>=2, J>=3,
C>W1>0, D>=A^2, K>1, and CD+1-A>0, so G>0. Furthermore
H-C=B1+(j-1)C>0 and Q>W1^2+2>0. Thus u,v>0, and

    0<v/u=Q/J+(H-C)/F <= Q+H-C=:Mdiv.

Set

    V0=PK, t0=iJC,
    S0=t0(8D^2-4D-1), V1=S0GH.

Since E=t0 DC, exact identities give

    DF=t0^2D^3(D-1)+D,
    S0^2-64DF=t0^2(8D+1)-64D >=8D+9>0.

The last inequality uses t0^2>=9 and D>=1. Also S0>0, I<=G^2H^2, and
V0^2-a0=K^2-1>0. Therefore a0,a1 are positive and

    sqrt(a0)<V0, sqrt(a1)<V1.

Now define

    Omega=u(2mu-1),
    Theta=un+v-Omega(Mdiv+V0V1),
    F9=(Theta^2-Omega^2(a0+V0^2a1))^2-4Omega^4V0^2a0a1.

This is the primary equation. Omega never vanishes. Its exact four-factor
factorization over the complex numbers implies that any zero has
Theta/Omega=r0+V0r1 for roots r_i^2=a_i, with signs absorbed in the roots.
This rational number cannot vanish: otherwise |r1|=|r0|/V0<1, contrary to
the positive integer a1. The identity

    2(Theta/Omega)r0=(Theta/Omega)^2+a0-V0^2a1

then makes both roots rational, hence integers. No square-class independence
assumption is involved. The strict root bounds yield |r_i|<=V_i-1 and

    Z0=Mdiv+V0V1+r0+V0r1 >= Mdiv+1>0.

The selected factor equation is n+v/u=(2mu-1)Z0. Its left side is positive,
so mu>0. Its right side is integral, so u|v. Thus every zero recovers exactly
the four ratio conditions.

Conversely, if those conditions hold, choose any integer roots r_i and set
n=(2mu-1)Z0-v/u. This is an integer >=Mdiv+1-v/u>=1, and makes the selected
factor vanish. This proves the finalizer equivalence in both directions and,
combined with the compiler contract, the claimed Con(ZFC) equivalence.

## 7. Exact degree, not a degree upper bound

Diagonal specialization of all nine natural inputs to T yields explicit
nonzero leaders for every decisive register. Write a=2^kappa and
c=2^(15kappa/2-10). Some decisive degrees are

    L 11483; N 5932; R 22966; P 81527; K 81528;
    A 46696; C 22966; D 139324; E 231953; F 557298;
    G 719588; H 22967; I 1485110;
    a0 326110; a1 2181732; mu 187153; u 603994;
    V0 163055; V1 1090866; Omega 791147.

A raw degree walk is insufficient because V1^2-a1 has leading cancellation.
The certificate circuit uses the exact identity

    deltaV=V1^2-a1
      =[t0^2(8D+1)-64D]G^2H^2 +64DF(H^2-1).

Its first term dominates, giving degree1763760 and leader
2^147 a^881800 c^96. Put E0=un+v-Omega Mdiv. Then exactly

    Theta^2-Omega^2(a0+V0^2a1)
      =E0^2-2E0 Omega V0V1+Omega^2V0^2 deltaV-Omega^2a0.

The third summand dominates, with degree3672164 and leader
2^299 a^1835914 c^224. The final subtracted term
4Omega^4V0^2a0a1 has degree5998540, strictly below7344328. Hence

    deg(F9)=7344328,
    diagonal leading coefficient=2^598 a^3671828 c^448 >0.

The generated certificate records every decisive degree and exact leader,
with unknown coefficient-dependent low-degree heads left unknown, not guessed.
There are no unresolved positive-degree cancellations in that circuit. Since
the diagonal attains the multivariate total-degree upper bound, equality is
proved. The main and certificate circuits are exactly equal polynomials by
the displayed identities, independently corroborated by modular replay.

## 8. Positive translation, alternatives, and reproducibility

The positive variables are epsilon_plus,g,h,s,w,phi_plus,i,j,n_plus, each >=1.
Substitute each for its natural counterpart plus one. In particular
b=epsilon_plus+1, phi=phi_plus-1 and n=n_plus-1. This is a bijection of domains,
not a parametrization of unrestricted integers, and preserves total degree.

The conservative three-block alternative uses the same sparse source but
N=L=B^5741 and R=(L-1)[(Scode+Tcode+1)L+Tcode+1]. The standard complement
identity gives pop(R)=2log_2(L)-tau_2(Scode,Tcode). The same ratio interface and
finalizer therefore prove its equivalence. Its source bounds follow directly
from Section3. Its exact degree is12023320; its nonmonomial positive diagonal
leader is explicitly certified, rather than assumed not to cancel.

For the uncalibrated comparison the stronger bound Scode+Tcode<B^5741
also holds: Jcode<Z/64, (B-2)A_targets<B^5191=Z/B^366<Z/128,
and (g+Mcode)/N0<2<Z/128. Their sum is less than Z.

The uncalibrated two-block comparison uses b=2(epsilon+1)^2, B=ab^2,
L=B^5741 and N=2^(17kappa/2-9)B^2965(epsilon+1)^3. Here the tested threshold
is 2^(5947kappa-21)b^11863; substitution of b makes this exactly N^2.
The choice admits every b=2^(2r+1) by epsilon=2^r-1, and this sequence is
unbounded. Hence completeness can choose b>max x_i; no unsupported sparse
cofinality step is used. Its higher exact degree14687132 is why it is not the
primary result. These alternatives are included to make the design tradeoff
and discarded restriction auditable.

Run `python3 nine/build_nine.py` and `python3 nine/verify_nine.py` from the
package root. Only Python's standard library is required. The checks rebuild
all twelve primary/translated/certificate/alternative circuits, authenticate
the complete four-port tuple, independently expand the original positive
source, verify all26 recipe bounds, replay360 modular assignments and11520
named registers, exercise43945 two-block cases, test42 threshold identities,
expand the near-square identity exactly, and check243 majorant and1728
finalizer-completeness fixtures. `generated/VALIDATION.json` records the run.
These checks test the implementation and finite data, not consistency itself.
