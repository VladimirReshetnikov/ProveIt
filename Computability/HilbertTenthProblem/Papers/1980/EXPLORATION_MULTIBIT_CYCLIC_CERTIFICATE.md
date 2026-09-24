# A 70-operation cyclic certificate for every fixed finite four-cell relation

The multi-bit cell compiler integrates with cyclic transport, inverse
mask packing, and the fixed-minus Pell kernel in **70=40M+30A**. The
certificate has three supplied positive parameters `q,P,C`, 23 positive
existential unknowns, and 16 equations. Its operation count is independent
of the finite alphabet and local truth table. The fixed numerals can be
extremely large; they have no construction cost in the chosen measure.

This is a complete certificate for the encoded cyclic predicate stated
below. The rule, alphabet, and state coding are fixed before its three
parameters vary. It does not provide a raw numerical input and halting
interface for one fixed universal rule. In particular, this70 does not
replace the established89-operation universal certificate.

The [checker](../verification/explore_multibit_cyclic_certificate.py) and
[receipt](../verification/explore_multibit_cyclic_certificate.json) contain
the source schedule and exact finite checks. The mathematical proof uses
the [multi-bit compiler](EXPLORATION_MULTIBIT_AFFINE_CELL.md) and the
[nonsquare-scale kernel argument](EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md).

## 1. Fixed constants and the precise predicate

Let `A` be a nonempty finite alphabet, with a fixed injective encoding

    Enc:A -> {0,1}^k minus {0}, k>=1.

Let `R4 subset A^4` be any finite relation on left, center, right, and
next. Its Boolean truth table requires that all four state codes belong
to `Enc(A)` and that the corresponding tuple belongs to `R4`. It rejects
the all-zero tuple. Apply the multi-bit compiler with `g=4`. Retain its
constants

    B=2^d, G0, DL,DC,DR,DY, MC,MF.

Here `MC` is the state mask and `MF` the local-field mask. A state cell
contains its `k` genuine bits and `m-k` arbitrary dummy bits, in the
compiler's sparse positions. The scalar local expression is

    Fcell=G0+DL*Lcell+DC*Ccell+DR*Rcell+DY*Ycell.          (1)

For any four typed cells, even with invalid projected states, the compiler
proves

    0<Fcell<=B-2,
    Fcell AND MF=0 iff their projected tuple is in R4.   (2)

Every permitted state cell is even and at least2, because its genuine
code is nonzero. All coefficients are positive. Their construction also
gives

    0<DL,DC,DR,DY<B,  0<G0<B-1,
    0<MC,MF<=B-2, MC odd, MF even,
    popcount(MC)+popcount(MF)=d.                        (3)

For example, each coefficient `Ds` has inner-radix degree `k-1` and
coefficients smaller than the inner radix; this puts it below `B`, whose
degree is `k+m-1`. The guard is one positive term of the scalar expression,
so (2) with all bits zero gives `G0<=B-2`. Both masks are positive; `MC`
omits at least one position and `MF` is a positive even number below `B`.
The compiler with four sites has `B>=16`.

The predicate on supplied positive integers `q,P,C` is

    q=B^N, P=B^h, 1<=h<=N,
    C=sum_{i=0}^{N-1} C_i B^i,

where every `C_i` is a permitted encoded alphabet state with arbitrary
dummy bits, and, for every index modulo `N`,

    R4(state(C_(i+h)),state(C_i),
       state(C_(i-h)),state(C_(i-h-1))).                (4)

Different dummy fillings describe the same projected configuration but
are different numerical parameters. No quotient of those numerical
representations is implicit in the statement.

## 2. Exact transport and a positive quotient

For decoded geometry put `D=q-1` and `J=D/(B-1)`. Write `L,R,Y` for the
cyclic shifts of `C` whose digits have indices `i+h,i-h,i-h-1`. Then

    PL=C+kL*D, R=PC-kR*D, Y=BPC-kY*D,
    PJ=J+align*D, align=(P-1)/(B-1).                    (5)

The wrap quotients satisfy `0<=kL<P` and `kR,kY>=0`. The actual local word

    Factual=G0*J+DL*L+DC*C+DR*R+DY*Y                  (6)

has no intercell carry and lies in `[1,(B-2)J]`, hence strictly between
zero and `D`. For

    E=DR+B*DY,
    K(P)=DL+P(DC+E*P),

where `E` is one fixed numeral, equations (5) give

    K(P)C+G0*J-P*Factual=z*D,
    z=P(DR*kR+DY*kY)-DL*kL-G0*align.                   (7)

Every genuine state cell is at least2, so `C>=2J` and

    kY=floor(BPC/D)>=floor(2BP/(B-1))>=2P.

Using `DY>=1`, (3), `kL<=P-1`, and `P>=B`, we get the uniform strict bound

    z>=2P^2-[DL+G0/(B-1)](P-1)
      >2P^2-B(P-1)>0.                                 (8)

No sign adapter or assumption about the particular transition rule is
needed. The ten-operation factored equality is

    P[(DC+E*P)C-F]+DL*C+G0*J=z(q-1).                   (9)

Its source counts `E*P,+DC,*C,-F,*P,DL*C,+,G0*J,+,z(q-1)`.
Thus it costs `6M+4A`. The subtraction is an integer-valued computed
register; soundness does not assert its positivity.

## 3. Complete source and its operation ledger

In addition to `q,P,C`, supply the positive outer unknowns

    v,J,align,F,alpha,z

and the seventeen positive kernel unknowns

    a,c,d,f,h0,i,j,k,o,r,s,w,tau,eta,zeta,gamma,yaux.

Construct by counted operations

    Lambda=q*q, D0=Lambda*q=q^3,
    S=C+qF, M=(MC+q*MF)J.                              (10)

The six outer equations are

    (B-1)J=q-1, Pv=q, (B-1)align=P-1,
    C+alpha=q,
    P[(DC+E*P)C-F]+DL*C+G0*J=z(q-1),
    r=(Lambda-S)(Lambda-1)+M.                           (11)

For `X=wD0`, `Yp=sD0`, `Delta=a^2+4a+3`, and `u=jc-(2r+1)`, retain the ten
fixed-minus kernel equations

    XYp^2(XYp^2+1)k^2=tau(tau+1),
    c=Yp*k+eta, k=eta+zeta, k=r+1+h0*XYp,
    a=Yp(X+1), d=X+ac+gamma(4a+3),
    d^2=Delta*c^2+1,
    (ic^2)^2=Delta(f^2-1),
    Delta(f^2-1)(u^2-yaux^2)=1-yaux^2,
    u=of-c.                                            (12)

The schedule shares the preceding norm residual in the auxiliary norm,
with the same exact acyclic correction as the retained43-operation
kernel. Its name `n2` denotes `D0`; it assumes no square root before
power decoding. Equality comparisons and fixed numerals are free.

| Part | M | A | Total |
|---|---:|---:|---:|
| Geometry |3|2|5|
| `C+alpha=q` |0|1|1|
| Factored local equality (9) |6|4|10|
| `Lambda=q*q,D0=Lambda*q` |2|0|2|
| `S=C+qF` |1|1|2|
| `M=(MC+q*MF)J` |2|1|3|
| Packed index in (11) |1|3|4|
| Outer subtotal |15|12|27|
| Fixed-minus kernel |25|18|43|
| **Complete source** |**40**|**30**|**70**|

No affine coefficient or transition-table entry is a supplied unknown.
All constants are effectively determined by the fixed finite relation.

## 4. Bounds and kernel decoding in a sound order

Take any positive solution of (11)--(12). Geometry gives `q>=P>=B>=16`
and `J>0`; the explicit low-field bound gives `0<C<q`. The mask bounds in
(3) and the repunit equation imply, without yet decoding any power,

    0<M=J(MC+q*MF)
       <=(B-2)J(q+1)<(B-1)J(q+1)=q^2-1.              (13)

If `S>=Lambda+1`, positivity of `r` contradicts the last equation of
(11). Hence `S<=Lambda`. Since `C>0`, this implies `F<q`. Now `C<q` and
`F<q` give `S<Lambda`; in particular, `S=Lambda` cannot hide an overflow.
Consequently

    q^2<=r<q^4, D0=q^3<r^2.                            (14)

Indeed, `r>=Lambda-1+M>=Lambda` and `r<Lambda^2`. These are exactly the
pre-power estimates used by Sections4--5 of the69-operation cyclic
proof. In particular,

    X,Yp>=q^3, XYp>=q^6>r+1,
    a>q^6>2r+1, 4r/a<4/q^2<=1/64.

The retained first-index, auxiliary-index, exponent-congruence, and
ratio arguments therefore apply at the actual divisor `D0`, yielding

    X=2^(2r+1),
    Yp=floor((X+1)^(2r)/X^r),
    D0 divides binom(2r,r).                             (15)

This use of the retained kernel relies on the explicitly proved
nonsquare-scale argument, not on assuming that `q^3` is initially a
square. The signs of computed registers are handled there as well.

As `q^3` divides the power of two `X`, `q=2^e`. Since `B=2^d` and
`B-1` divides `q-1`, the standard identity
`gcd(2^d-1,2^e-1)=2^gcd(d,e)-1` implies `d|e`. Thus `q=B^N`. Similarly
`P|q` and its alignment equation give `P=B^h`, with `1<=h<=N`.

## 5. Mask recovery proves exact local validity

In the decoded geometry the two mask fields are disjoint, and (3) gives

    popcount(M)=dN, log2(Lambda)=2dN.

The inverse-packing identity, including its strict overflow case, says
for `0<S<Lambda=2^(2dN)` and `0<=M<Lambda` that

    popcount((Lambda-S)(Lambda-1)+M)
      <=log2(Lambda)+popcount(M)=3dN,

with equality exactly when `S AND M=0`. By (15) and
`v2(binom(2r,r))=popcount(r)`, this upper bound is attained. The strict
field bounds already established in Section4 separate the two fields:

    C AND (MC*J)=0, F AND (MF*J)=0.                     (16)

The first identity types every digit of `C` into the compiler's permitted
Boolean positions. At this point a projected code might still be invalid;
the relation test will reject it. Construct the actual cyclic neighbors
and their exact field (6). The compiler bound (2) holds for all typed bit
tuples, so `0<Factual<D`. Equation (9) makes `P(F-Factual)` divisible by
`D`. Since `P` is invertible modulo `D`, and `0<F<q`, the only possible
representative is `F=Factual`. This remains true if `F=D`, since
`Factual` is strictly between zero and `D`.

The second identity in (16) and the scalar truth equivalence (2) now prove
both genuine state validity and the intended relation at every cell.
Every cell appears as the center of a tested tuple. Thus the exact
predicate (4) follows. No nonzero-state hypothesis was assumed before
the truth test; it is used only for the positive converse below.

## 6. Positive completeness at the actual new index

For a word satisfying (4), choose `v=q/P,J=(q-1)/(B-1)`,
`align=(P-1)/(B-1)`, `F=Factual`, `alpha=q-C`, and the quotient (7).
All six are positive integers by the digit bounds and (8). Form the
actual `S,M,Lambda,D0,r` of (10)--(11). Its masks vanish on the valid word,
so the inverse identity gives `popcount(r)=3dN` and hence the divisibility
in (15).

Both `C` and `qF` are even, whereas `MC` and `J` are odd. Thus `S` is
even, `M` is odd, and the actual new `r` is odd. Also (14) holds. The
positive kernel extension from Section7 of the69-operation proof can
therefore be instantiated afresh at this `r,D0`. Explicitly, set

    j0=2r+1, X=2^j0, w=X/D0,
    Yp=floor((X+1)^(2r)/X^r), s=Yp/D0,
    a=Yp(X+1), A0=a+2, Delta=A0^2-1, E0=XYp,
    P0=2XYp^2+1, c=psi_A0(j0), d=chi_A0(j0),
    k=psi_P0(r+1), eta=c-Yp*k, zeta=k-eta,
    tau=(chi_P0(r+1)-1)/2, h0=(k-r-1)/E0,
    gamma=(d-X-ac)/(4a+3),
    m0=2c*j0, f=chi_A0(m0), R0=Delta*psi_A0(m0),
    i=R0/c^2, yaux=psi_R0(j0), u=chi_R0(j0)/R0,
    j=(u+j0)/c, o=(u+c)/f.                             (17)

Here `psi,chi` are the second and first Pell coordinates. The ratio
bounds give `0<eta<k`; the retained congruences and strict growth give
positive integral `w,s,tau,h0,gamma,i`. Since `j0=3 mod4`, the fixed-minus
identities give `u=-j0 mod c` and `u=-c mod f`, making `j,o` positive
integers. These arguments, with the other positive coordinates in (17),
verify all ten equations (12). The witness tuple is constructed at the
new index, rather than reused numerically from another packing.

Thus all positive existential coordinates exist, completing the converse.
The astronomical size of these coordinates does not change the source
operation count; numerical materialization of an entire packed Pell
tuple is not asserted.

## 7. Computational meaning and the remaining interface

Every valid cyclic word pulls back to a totally periodic configuration
by `a(x,t)=state(C_(-hx-(h+1)t mod N))`. The index map is surjective
because `(x,t)=(i,-i)` maps to `i`. The four-cell rule is therefore obeyed
everywhere. Conversely, a torus of width `h+1` and height `h` has such a
cyclic presentation of length `h(h+1)`.

The [four-cell period lift](EXPLORATION_FOUR_CELL_PERIOD_LIFT.md) gives
such presentations for independently padded marked Turing tableaux.
Combining these results requires an actual marked occurrence and an
accounted raw-input interface. The present theorem supplies the general
arithmetic component, with all geometry, typing, mask, and positive Pell
obligations included. It does not silently identify varying finite-table
constants with a fixed machine index and a freely varying raw input.

## 8. Verification evidence

Independent complete scoped mathematical/source review passes for both
positive directions. The source checker compares all70 primitives and
16 residuals, including the retained acyclic auxiliary correction.
Independent recomputation of the symbolic source and2,880 preliminary
bound candidates matches the saved receipt;1,296 positive-index cases
use non-power values of q.

The numerical examples cover2,180 cyclic word/stride/dummy combinations,
with182 accepted: a singleton alphabet, three-state membership, and a
three-state directional rule requiring next=left. The directional example
rejects45 tuples with genuine states but incorrect transitions. A
nonconstant length-three word passes at stride1 and fails at stride3,
under all three dummy patterns. These tests distinguish correct neighbor
transport from merely checking state membership. Constants up to a
124,608-bit radix exponent in the membership example are handled exactly;
receipts record bit lengths and hashes rather than printing huge numerals.

The retained kernel regressions cover five main odd indices through r=65
and five auxiliary examples. They are component regressions, not numerical
materializations of the full packed witness construction (17). The
standalone checker recomputes the JSON receipt, normalizing tuple-valued
equation pairs to their JSON list representation before comparison.
A final fresh default run passes with exact equality to the saved receipt.
