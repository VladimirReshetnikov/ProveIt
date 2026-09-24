# Shared transport scaling for either first appendant symbol

Review status: author and two independent complete proof/source reviews and
fresh verification runs passed without findings. The construction and
arithmetic are frozen. The published106 certificate and the separate
zero-leading105 construction are unchanged.

For **every fixed binary appendant of length at least two**, the established
encoded-word tag interface has a complete **105-operation certificate:
53 multiplications and 52 additions/subtractions**, with **34 positive
existential unknowns and 21 equations**. Both original input parameters
are retained. The deletion number beta may be any positive integer.
There is no restriction on the appendant's first symbol, no shifted input
length parameter, and no ordinary numerical-input or universal operation
claim.

The construction chooses one of two schedules from the fixed appendant.
Each schedule costs105. This compile-time choice is not a supplied unknown
or a runtime branch depending on the queried word.

## 1. Constants and the two exact content coordinates

Retain the106 constants and encoded-input contract:

    K=3^beta, Kh=K/3, B=3^(a-1), c=(Kh-1)/2,
    U=value(u), C>max(K,3^a,2U+3),
    Linit=3^|w|, Ninit=value(w), |w|>=beta.

Here a>=2, so B>=3. Both u and w have digits zero or one in little-endian
radix three. The fixed power of three C is divisible by Kh. Define fixed
integer numerals

    Cbar=C/Kh, epsilon=U mod 3 in {0,1}, U3=(U-epsilon)/3.

Epsilon is the first symbol of the fixed appendant. The constants are
chosen before the queried word; no arithmetic division is performed.

Replace the supplied positive coordinate F_N by positive F_T and compute
T=F_T-1. Reuse the existing twice_Q=2Q and M1=twice_Q+S1. Compute N by
the fixed choice

    epsilon=0: N=3T+S1,
    epsilon=1: N=3T-twice_Q.                              (1)

The zero-leading case is the preceding restricted105 construction. For the
one-leading case N can be negative before the kernel; the proof below
explicitly handles this new possibility. T remains nonnegative and is not
an additional Boolean mask field.

In both cases the exact identity is

    N-3E-S1+U M1=3(T-E+U3 M1).                            (2)

For epsilon=1, use M1=2Q+S1 to cancel the additional term M1-2Q-S1.
This relation is an actual computed identity, not an assumed selector
interpretation.

Compute the shared transport register D=Cbar*A and retain the paid radix
comparison Kh*D=R. The two new transport equations are

    D(T-E+U3 M1)=N-Ninit+q Nfinal,
    D(L+(B-1)M1)=L-Linit+q Lfinal.                       (3)

All eight other outer sources and all eleven44-operation kernel sources
are the106 sources after substituting(1). The conceptual mask order is
unchanged:

    Gstar, Q, S0, S1, M0, M1, Ebar, E, Nbar, N,          (4)

with S0=H-S1, Gstar=Q+AH+S0, M0=L-M1, Ebar=cH-E and
Nbar=Nsum-N. The106 factored computation still evaluates exactly this P.

## 2. Exact source correspondence

Let f0=Kh*Cbar*A-R be the retained radix residual, and let fC,fL be the
new residuals in(3), left minus right. With O=T-E+U3 M1 and
OL=L+(B-1)M1, the old106 transport residuals satisfy

    old_content=3Kh*fC-3*f0*O,
    old_length=Kh*fL-f0*OL.                              (5)

These are unrestricted polynomial identities. Every other outer residual
and the packed index agree exactly after the corresponding formal
substitution

    epsilon=0: F_N=3F_T+F_S1-3,
    epsilon=1: F_N=3F_T-2F_Q.                            (6)

The first expression is already positive for all supplied positive tuples.
The second need not be, so(5)--(6) alone are not used as a positive-domain
embedding in that case. Positivity is recovered next, before invoking the
complete106 theorem.

## 3. Pre-power length bounds, independent of N's sign

The initial and geometry sources imply

    A>Linit>=K, R=CA>K^2, q>=R>9,
    H=(q-1)/(R-1)>0.

The length source in(3) is equivalent, using the positive fixed Kh, to
the original106 source

    R[L+(B-1)M1]=Kh(L-Linit+q Lfinal).

Because L>0, M1=2Q+S1>=0, B-1>=2 and Lfinal<K, the retained bounds are

    L<K^2*q/(3R-K)<q/2,
    0<Nsum=(L-H)/2<q/4,
    M1<7q/36, Q<7q/72, S1<7q/36.                        (7)

In particular the new coordinate satisfies, in either branch,

    N>=-2Q>-7q/36.                                       (8)

For epsilon=0 this is weaker than the immediate N>=0; for epsilon=1 it
follows from T>=0. No content mask or decoded history has been used.

The conceptual first six fields retain their individual upper bounds
strictly below q, even when a complement is negative. In particular
M0<q/2, S0<=H<q and Gstar<q/4+q/3<q. Let Plo6 be their formal packing.
The complete polynomial, rather than an unsigned-field interpretation,
also proves it strictly positive:

    Plo6=H(A+q^2+1)+(q+1)Q+(q^3-q^2-1)S1
           +q^4[L+(q-1)M1]>0.                          (9)

Every coefficient in(9) is nonnegative for q>=2 and the H term is
positive. Each of the original six conceptual fields is an integer at
most q-1, so their weighted sum is at most
(q-1)(1+q+...+q^5)=q^6-1, even if some fields are negative.
Thus Plo6<q^6. These claims do
not require S0,Gstar or M0 already to be recovered as Boolean fields.

## 4. The signed packing still supplies the kernel hypotheses

The remaining two combined pairs are

    TE=cH+(q-1)E>=0,
    TN=Nsum+(q-1)N,
    P=Plo6+q^6 TE+q^8 TN.

Using(8)--(9) and positive Nsum gives the strict lower bound

    P>q^8(q-1)N>-7q^10/36.                              (10)

Write D0=q^10 for the kernel scale. The unchanged index and positive bound
equations are

    2r+1=D0+2P, r+betaP=D0.

Thus, even if N or P has not yet been proved nonnegative,

    r>11D0/36-1/2>D0/4, r<D0.                           (11)

The paid q>9 implies D0>=81, r>=27 and D0<r^2. Together with r<2D0,
these are precisely the hypotheses of the reviewed generic theorem in
`EXPLORATION_PARITY_FREE_PELL_KERNEL.md`. No premise P>0 is needed by
that theorem, and none is assumed here.

The kernel forces q to be a power of three. The retained positive
geometry then gives R a power of three and q=R^t. Its central-binomial
condition, with r<D0, is the direct native unit-two mask from
`EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`: r has unit trit2 and every
higher trit1 or2 up to the scale. Therefore

    P=r-(D0-1)/2

is a Boolean ternary word with unit trit1. In particular **P>=0** has now
been proved without assuming N>=0 in the kernel bootstrap.

## 5. A negative reconstructed N contradicts the packed mask

Assume for contradiction that N<0. The integer N is then at most -1.
The old content source follows algebraically from(5), regardless of N's
sign. Rearranging it gives

    3E=(1-K/R)N-S1+U M1+K*Ninit/R-K*q*Nfinal/R.

Here 1-K/R>0, while S1 and Nfinal are nonnegative. Consequently

    3E<U M1+K*Ninit/R.                                  (12)

The length source and L<q/2 imply

    R(B-1)M1<Kh(K+1/2)q.

For a binary appendant U<3B/2 and B>=3, so U/(B-1)<9/4. Since R>K^2
and K>=3, it follows that

    U M1<3K(K+1/2)q/(4R)<7q/8.

The specified input has Ninit<Linit/2<A/2, giving K*Ninit/R<K/(2C)<1/2.
Equation(12) therefore yields

    E<7q/24+1/6<q/3,                                   (13)

where q>9 is more than sufficient for the final inequality.

The fixed c satisfies c<R-1, so cH<q. From(13), the nonnegative prefix
pair has

    0<=TE=cH+(q-1)E<q^2.

This is a numerical bound on the whole pair; it does not presume Ebar>=0.
Together with 0<Plo6<q^6 and integrality it proves

    0<Plo8=Plo6+q^6 TE<q^8.                             (14)

On the other hand, Nsum<q/4 and N<=-1 imply

    TN=Nsum+(q-1)N<=Nsum-q+1<1-3q/4<-1.

Hence P=Plo8+q^8 TN<0, contradicting the decoded mask. We have proved
N>=0. This exclusion does not require individually decoding the low six
fields first; their polynomial bounds(9) and the whole-pair bound(14)
suffice.

Now F_N=N+1 is positive. Equations(5)--(6) give a positive106 solution
with the same packed integer, index and all kernel witnesses. The complete
106 theorem proves the input word halts. All of its later individual-field
and first-halt reasoning is available without a new assumption or interface.

## 6. Canonical completeness for both fixed choices

Suppose the specified computation halts and stop at its first genuine
halt. In source row j let n_j be its word value, s_j its first symbol,
and m_j=3^(word length). Every source word is nonempty. The canonical
selected interval is Q_j=s_j(m_j-1)/2, and n_j=s_j modulo3.

For epsilon=0,

    T_j=(n_j-s_j)/3

is a nonnegative integer. For epsilon=1,

    T_j=(n_j+2Q_j)/3

is likewise integral and nonnegative: if s_j=0 then Q_j=0 and n_j is
divisible by3; if s_j=1 then 2Q_j=m_j-1 is -1 modulo3, cancelling the
unit digit of n_j. Aggregate T=sum T_j R^j and take F_T=T+1.

Every other supplied coordinate is the canonical106 coordinate at the
same width. Formula(1) reconstructs exactly its N. The paid shared D is
positive, and(2), R=KhD and the old transports imply(3). All ten
conceptual fields, P, r, scale and positive packing slack are unchanged.
The same seventeen positive Pell auxiliaries therefore work for either
parity of the index. Zero T or terminal content is represented by a
positive adapter equal to one.

This proves completeness for every fixed binary appendant of length at
least two with the original input parameters (Ninit,Linit). The argument
does not require a claim that every formal106 continuation beyond an
earlier halt satisfies a chosen quotient representation. Canonical histories
stopping at their first halt suffice for positive existence equivalence.

## 7. Full operation count and fresh evidence

In either compile-time branch, the new content adapter uses one extra
multiplication and one extra addition/subtraction. Removing the old3E
and its addition of S1 saves exactly those two operations. Computing
D=Cbar*A and R=KhD adds one multiplication to the old radix computation;
removing the two transport right-side products saves two multiplications.
Both left products, terminal products and joins remain counted. The net
saving from106 is one multiplication: **105=53M+52A** in both branches.

F_T replaces F_N, so there are still34 positive coordinates and21
equations. D is a computed register. The existing twice_Q is computed
once and reused in the one-leading reconstruction; N is scheduled after
that register exists. The packing computation itself is unchanged.

`../verification/explore_general_scaled_tag_transport.py` independently
constructs both complete schedules, all42 source checks across the two
branches, the unchanged norm correction at index18, both identities(5),
and exact preservation of P under the formal coordinate substitutions.
It checks768 further off-equation identity tuples, including192 negative
reconstructed contents and failed radix geometry.

The signed bootstrap regression checks eight exact rational bounds,
including nonpower q. It then tests37,824 negative-content pair states
within the proved N<0 and E<q/3 ranges, sampling extremal prefix bases
and lower blocks. Every such state has negative P and fails the exact
native valuation. These states are explicitly necessary-range tests, not
claimed complete tag source tuples.

Fresh canonical construction evaluates both actual105 and106 prefixes
on776 halting histories with2,006 source rows. The fixed-zero branch
accounts for448 histories/1,238 rows, and the fixed-one branch for328
histories/768 rows. Each example checks all ten outer comparisons in
both versions, every mask field and the exact native index valuation.
All776 indices are preserved:514 are even and262 odd. There are85
zero-T histories and632 zero-terminal histories. The400 runs reaching
the finite cutoff remain unclassified.

Enormous Pell auxiliaries are not materialized; their complete positive
existence and preservation follow from106. The shifted-marker alternative
is not part of this certificate, and no appendant recoding, input-length
adapter, runtime selector branch or universal numerical-input claim is
being hidden in the count.
