# A compiled initial-length bound gives a 92-operation tag certificate

The paid comparison Linit+alphaI=A can be removed from the reordered93
source when the admitted input length satisfies K^2 Linit<C. The complete
new source has **92 operations = 51 multiplications + 41 additions/subtractions**,
with **28 positive unknowns and17 equality comparisons**. All nine masks,
both transports, true radix geometry and the fixed-plus43 kernel remain.
The encoded input is unchanged.

Soundness is actual eventual halting for every valid encoded input in the
explicit domain K^2 Linit<C. Completeness on that domain has the same startup
promises as93: beta>=2, first symbol0, a nonzero bit beyond the head in the
initial deleted prefix, a genuine selector-one event, and a genuine terminal
word consisting of the single symbol0. There is no even-beta restriction.

Neary's designated input has length a-beta+1, where a is the fixed
appendant length. A freely enlarged compiler constant therefore supplies
the domain condition without a new runtime operation. This remains an
encoded-instance result, not a universal raw numerical input bound.

The proof and checker are new;93 and all published predecessors are unchanged.
Author and two independent complete proof/source reviews and fresh
verification runs pass. The companion
[receipt](../verification/explore_compiled_initial_tag_bound.json) records
the exact sources and finite evidence.

## 1. Exact source and admitted input domain

Use the constants and positive coordinates of
[the reordered93 source](EXPLORATION_REORDERED_STARTUP_TAG.md):

    K=3^beta, k=K/3, B=3^(a-1), U=value(appendant), a>=2,
    cc=(k-1)/2, epsilon=U mod3, Ut=(U-epsilon)/3,
    j=(C-C/K)/2.

Choose the fixed power of three C so that

    C>max(K^3,3K*3^a,2KU+3).                         (1)

The arithmetic theorem applies to valid specified inputs

    Li=3^ell, ell>=beta, Ni Boolean, 0<=Ni<Li/2,
    K^2 Li<C.                                      (2)

For the application in Section6, the last condition is a consequence of
the fixed input length. It is an explicit input-domain condition in the
general theorem; it is not inferred for arbitrary unbounded input lengths.

Supply the same strictly positive Q,S1,T,E as93, and compute

    M1=2Q+S1,
    N=3T+S1         if epsilon=0,
    N=3T-2Q         if epsilon=1,
    D=(C/k)A.

Delete the positive coordinate alphaI, the instruction

    initial_bound=Li+alphaI,

and its comparison with A. The seven remaining outer comparisons are

    kD=R,
    D(T-E+Ut*M1)=N-Ni,
    D[L+(B-1)M1]=L-Li+3q,
    H(R-1)=q-1, Rv=q,
    2r+1=q^9+2P, r+betaP=q^9.                       (3)

The nine conceptual fields and the exact packing remain those of93:

    S0=H-S1, S1, Q, G=Q+AH,
    M0=L-M1, M1, Ebar=ccH-E, E, GN=N+jAH,

    TE=ccH+(q-1)E,
    Rest=L+(q-1)M1+q^2[TE+q^2 GN],
    P=H+(q-1)S1+q^2[Q+q(Q+AH)]+q^4 Rest.           (4)

Deleting one addition from93 gives92=51M+41A. Removing alphaI and its
comparison gives28 positive coordinates and17 equations: seven outer and
ten kernel equations. The fixed endpoint product l_end=q*3 remains charged.
The computed-u norm-source correction is now at zero-based comparison15.

The checker expands all source polynomials in both fixed leading branches.
Its formal substitution alphaI=A-Li verifies that all other source and
packing polynomials remain identical. This substitution may be zero or
negative: it is not a positive inverse witness map. In particular the proof
does not lift every92 tuple to a93 tuple at the same width.

## 2. Pre-mask bounds without A>Li

Only A>=1 is initially known. Equations(1)--(3) give

    R=CA>=C>K^3>K^2, q>=R>108,
    H=(q-1)/(R-1), K^2 Li<R,
    K Ni/R<K Li/(2C)<1/(2K)<1/2.                   (5)

The inequality q>=R follows either from positive v or from positive H.
There is no power or Boolean premise in(5). The length equation gives

    (R-k)L+R(B-1)M1=k(3q-Li)<kKq.

Here beta>=2 gives K>=9, while L,M1>0 and B>=3. Since R>K^2,
the estimates in the single-content-guard proof remain valid:

    0<L<q/2, 0<M1<q/6,
    0<Q<q/12, 0<S1<q/6, N>-q/6.                   (6)

For L use R-k>2kK. For M1 use kK/R<1/3 and B-1>=2.
The signed bound on N follows from T>0 and 2Q<M1 in either branch.
Consequently

    jAH=(R-R/K)H/2>=(q-1)/3,
    GN>q/6-1/3>0.                                  (7)

All terms in the factored packing(4) are positive or nonnegative; L,H and
GN are positive. Thus P>0 before any field is known Boolean. The index and
positive packed slack give

    (D0-1)/2<r<D0, D0=q^9>=81,
    r>=27, r<2D0, D0<r^2.

These are the hypotheses of the unchanged fixed-plus43 soundness theorem.
It yields q a power of three and the native unit-two mask, hence P Boolean
with unit1 and P<D0/2. The positive terms below q^8 GN in(4) give

    0<GN<q/2, GN<=(q-1)/2, N=GN-jAH<=(q-1)/2.     (8)

No Boolean or nonnegative property of N is asserted.

The exact content identity is

    3E=(1-K/R)N-S1+UM1+K Ni/R.

The first term is at most (q-1)/2, including when N is negative. As
U<3B/2 and M1<q/[3(B-1)], one has UM1<3q/4. Replacing the old
input-slack estimate by(5) therefore gives the same strict bound

    E<5q/12+1/6<q/2.                                (9)

Every field before GN now lies in(-q/2,q), and the supplied Q,S1,E,
computed G and M1 are nonnegative. In particular

    G<q/12+AH<q/12+q/3<q,

because A/(CA-1)<1/3 holds even at A=1. Also S0<=H<q,
M0<L<q/2, and 0<=ccH<q/2 bounds Ebar above; their negative bounds
follow from(6) and(9). A negative next field would have q-remainder
greater than (q-1)/2 and could not be Boolean. Greedy recovery therefore
types all nine fields with no interfield carry. The first field S0 has unit1.

The retained q=Rv now makes R a power of three. The head equation gives
q=R^t for a positive integer t, and A=R/C is a power of three. All these
conclusions precede any interpretation of content rows.

## 3. The A=1 boundary is excluded by positive Q

The prior bound A>Li cannot be used to assert A>1. Instead suppose A=1
after the preceding recovery. Then G=Q+H. The words S0 and S1 partition
the row heads. Start at the first row with zero incoming carries.

At its head, Boolean G forces the Q digit to be zero: adding it to the
unit H digit would otherwise give2. The equation M1=2Q+S1 then emits
the head selector with no carry. At every later position in that row,
there is no S1 digit and no incoming carry, so Boolean M1 forces Q's
digit to remain zero. Neither addition has an outgoing carry. Repeat
the argument at each following head. It proves Q=0 globally.

The source supplies Q strictly positive, so A=1 is impossible. Since A
is a power of three, A>=3. The ordinary projector proof with G=Q+AH
therefore applies: an inactive row has Q=M1=0, and an active row has an
initial Q interval ending in one marker M1 at most A. No row carry escapes.
At an inactive head G has digit0 because A>1, whereas S0 has digit1;
at active heads S0 is zero. Thus the disjoint addition

    Gstar=G+S0

restores the old Boolean projector guard. This restoration is conceptual
and has no runtime operation. The A=1 argument is needed; blindly making
this addition at A=1 would be invalid.

## 4. Direct actual-halting soundness

The recovered fields satisfy the same length-flow and signed-content
identities as the complete single-content-guard104 proof, with fixed
terminal content0 and marker3. The only changes needed in its semantic
argument are the initial width estimates, which follow from(2):

    R/k>=C/k>3K Li>Li,
    K^2 Li<R.                                      (10)

Both length-edge multipliers R/k and B(R/k) are powers of three larger
than Li. Hence the carry-free length equation

    M0+M1+3q=Li+(R/k)M0+B(R/k)M1

gives one increasing unit path from Li to3q, whose within-row terminal
marker is3.
Before its first short marker, each edge advances one row and its marker
L_i satisfies K^2 L_i<R. Equation(10) starts this invariant. Zero edges
do not increase the marker. One edges start with L_i<=A, and

    K^2 L_(i+1)=K*3^a L_i<=K*3^a A<R

by(1). Thus no assumption Linit<A is required for the path or induction.

For completeness of the dependency check, put b=R/K, z=R/K^2 and
hK=(K-1)/2. Each guarded row has a signed content n_i in
[-hK b,b/2). Its actual content at an identified causal marker is
0<=v_i<L_i/2<z/2. The first discrepancy has n_i=v_i-sb with
0<=s<=hK. Booleanity of the guard implies s Boolean. The exact content
congruence and prefix masks give d_i=(v_i mod K)+s without modular wrap,
so an actual first1 cannot become an encoded first0.

If the encoded next marker is short, the actual successor is also short
by this selector monotonicity. Otherwise the next guarded row exists.
The unchanged estimate

    vstar=(v_i-(v_i mod K)+UM1_i)/K
          <z/(2K)+z/2<z

uses C>2KU+3 and the just-proved marker invariant. A discrepancy s>0
makes the next guard contain the forbidden beta-trit block K-s>hK.
Thus s=0, identifying the actual prefix and transition; the residual
transport continues with the exact next actual content. This is the
same induction proved in Sections4--5 of
[the single-content-guard104 theorem](EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md).
Every width or input estimate that previously used A>Li has been supplied
by(5) or(10). The induction proves actual halting without requiring a
positive value for A-Li or typing N itself.

## 5. Complete positive converse on the admitted domain

Suppose an input satisfying(2) and the positive-startup first-zero promises
has a genuine halt at the single zero word. Choose A to be a power of three
larger than every genuine source marker, as in93. This remains a permitted
existential choice; deleting the bound does not prohibit choosing a wide
witness. Use the same canonical coordinates and the wrapped zero-edge
cycle, retaining all positive Q,S1,T,E.

The stronger fixed C still satisfies every93 compiler inequality. Both
the unpadded and padded constructions satisfy its old input bound with
the chosen positive slack A-Li. Delete that slack to obtain the complete
new outer tuples. The packing and index are exactly unchanged at this C
and chosen width. The parity formula P=N+L+H modulo2 gives opposite indices
for the two tuples at an odd width exponent, for every beta>=2. Choose the
even index and apply the fixed-plus43 positive converse for all sixteen
kernel auxiliaries. No new arithmetic or input conversion is required.

This proves existence equivalence on the stated completeness domain.
It does not prove that every92 witness has a positive same-width inverse
alphaI; arbitrary solutions were handled by the direct soundness proof.

## 6. Why the compiler can absorb Neary's initial bound

For Neary's normalized encoded instances, the appendant has fixed length a
and the specified input is its suffix after deleting beta-1 symbols. Thus

    Li=3^(a-beta+1), K^2 Li=3K*3^a<C.

The cited source and startup/terminal facts are recorded in
[the positive-startup95 theorem](EXPLORATION_POSITIVE_STARTUP_TAG.md) and
[the zero-terminal normalization](EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md),
from [Neary's Lemma9 and Theorem11](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf).
Increasing the fixed power C in(1) changes only fixed compiler numerals.
It introduces neither a variable exponentiation nor a runtime input bound.
The designated encoded input is the same one as before.

This is a complete92-operation certificate for that encoded-instance family.
It is not a claim about unrestricted input lengths for a fixed C, nor a
fixed-appendant universal representation for ordinary numerical input.

## 7. Exact verification boundary

The checker verifies both complete92 schedules and all34 source comparisons,
including the signed formal alphaI substitution, unchanged packing and
retained q*3 product. Rational pre-power checks explicitly include A=1,
zero or negative A-Li, and nonpower R or q. They check the replacement
bounds and are not claimed to be full source tuples.

A separate complete small-word enumeration checks the A=1 projector
without presupposing Q=0, then confirms that every accepted case has Q=0
and therefore violates the supplied positive-Q domain. Fresh genuine traces
exercise both fixed leading branches, the fixed input-length relation,
odd and even beta, every new outer comparison, all nine masks, both wrapped
parity witnesses and the exact new index valuations. Positive Pell auxiliaries
are supplied by the proved converse rather than materialized. The finite
programs are arithmetic regression examples, not materialized Neary simulators.

The complete author run passed both92 schedules and34 source comparisons,
384 pre-power cases including64 with A=1,192 with negative formal alphaI,
64 with zero formal alphaI, and320 with nonpower R or q. The A=1 mask
enumeration checked1,400 candidates and accepted18, all with Q=0. It also
checked44 admitted genuine traces with370 source rows and88 full outer
tuples, including12 odd-beta histories. Both leading branches occur
(30 and14 histories); the canonical indices split24 even and20 odd.
The20 odd-index cases use the wrapped padding. One simulation cutoff
remains unclassified. Independent verification is pending.
