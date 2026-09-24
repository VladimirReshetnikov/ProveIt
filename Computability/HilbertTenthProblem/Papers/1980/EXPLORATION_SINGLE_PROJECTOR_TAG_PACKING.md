# A positive encoded-word tag certificate and its packing costs

Review status: author verification and the root and binary agents' independent
complete proof/source reviews and fresh verification runs all passed without
findings. The mathematical construction and arithmetic are frozen.

This is a complete arithmetic composition for the specified encoded binary
word in `EXPLORATION_TAG_TERMINAL_BOUND_RECOVERY.md`. Its explicit baseline
uses **115 operations = 55 multiplications + 60 additions/subtractions**,
**38 positive existential unknowns**, and **25 equations**. The two input
parameters are the ordinary integers Ninit and Linit, subject to the stated
external contract that they encode a binary word of length at least beta.
This is not a universal bound for an ordinary numerical query. Neither a
conversion from that query to the two encoded-word parameters nor a universal
startup contract for this binary tag program is supplied here.

The straightforward ten positivity adapters are deliberately retained. The
unadapted, nonnegative-word composition costs105. The earlier tentative104
general-input ledger missed a unit-digit condition; this note identifies it
and supplies an exact one-addition repair. No optimality claim is made.

## 1. Fixed program and complete outer equations

Fix beta>=1 and a nonempty binary appendant u of length a, for the rules
0->0 and 1->u. Use the predecessor's fixed numerals

    K=3^beta, Khalf=K/3, Af=3^a, B=Af/3,
    U=sum(u_i*3^i), c=(Khalf-1)/2,
    C a fixed power of three greater than max(K,Af,2U+3).

In particular C>=9 and B>=1. The specified input satisfies

    Linit=3^ell, ell>=beta,
    Ninit=sum(w_i*3^i), w_i in {0,1}, 0<=i<ell.

Supply positive F_Q,F_S0,F_S1,F_M0,F_M1,F_N,F_Nbar,F_E,F_Ebar
and F_Nfinal. Compute the ten nonnegative registers

    X=F_X-1  for X in {Q,S0,S1,M0,M1,N,Nbar,E,Ebar,Nfinal}.   (1)

These are ten paid subtractions. The other outer supplied coordinates

    A,H,R,L,q,Lfinal,alphaI,alphaH,v,r,betaP

are positive. The seventeen supplied auxiliary coordinates of the parity-free
44-operation Pell kernel are also positive, giving38 unknowns altogether.
The checker prefixes their names with `pell_` to avoid collisions.

Retain all ten outer comparisons of the31 predecessor:

    CA=R, S0+S1=H, 2Q+S1=M1, M0+M1=L,
    2(N+Nbar)+H=L, E+Ebar=cH,
    R(N-3E-S1+U M1)=K(N-Ninit+q Nfinal),
    R(M0+B M1)=Khalf(L-Linit+q Lfinal),
    Linit+alphaI=A, Lfinal+alphaH=K.                        (2)

The old G=Q+AH is still a computed register. Add the one operation

    Gstar=G+S0=Q+AH+S0.                                    (3)

The ten raw mask fields, in their packing order, are

    Gstar,Q,S0,S1,M0,M1,N,Nbar,E,Ebar.                      (4)

No field bound is supplied as an extra hypothesis or comparison: Section2
derives every one before invoking any mask. The row geometry adds only

    H(R-1)=q-1, Rv=q.                                     (5)

Computing q-1, R-1, the head product, and Rv costs4=2M+2A.
The already counted equation CA=R is shared. In particular no separate
repunit coordinate or equation q=2J+1 is needed.

Let P be the ordinary q-Horner packing of (4). Compute

    q2=q*q, q4=q2*q2, q8=q4*q4, D0=q8*q2=q^10,
    twiceP=P+P, index_rhs=D0+twiceP, packed_bound=r+betaP.

The final two outer comparisons are

    tr1=index_rhs, packed_bound=D0,                        (6)

where tr1=2r+1 is already computed by the44-operation kernel. There are14
outer comparisons. Add exactly the eleven kernel equations from
`EXPLORATION_PARITY_FREE_PELL_KERNEL.md`, Section3, at this D0 and r.
All25 expanded source polynomials and the115-instruction DAG are in the
companion checker and receipt. In particular, (1) and (3) are computed
register definitions, not additional equality comparisons.

## 2. Every field bound precedes power and digit decoding

This section uses only integer positivity, (1), (2), and (5). From the input
bound A>Linit>=K and the fixed C>K,

    R=CA>K^2, q=Rv>=R>1, H=(q-1)/(R-1)>0.                 (7)

Since B>=1 and M0,M1>=0, the length comparison gives

    R L <= R(M0+B M1)=Khalf(L-Linit+q Lfinal).

The terminal length bound Lfinal<K therefore yields

    (R-Khalf)L < Khalf*K*q,
    L < K^2*q/(3R-K) < q/2.                               (8)

For the last inequality, R>K^2 and K>=3 imply 3R-K>2K^2.
Consequently M0,M1<q/2. Containment gives N,Nbar<L/2<q/4,
and 2Q+S1=M1 gives Q<q/4. The head equation gives S0,S1<=H<q.
Similarly E,Ebar<=cH<q, since c<R-1. These statements include c=0:
both E and Ebar then equal zero and their adapters equal one.

Finally,

    Gstar=Q+AH+S0 <= Q+(A+1)H < q/4+q/3 < q.              (9)

Indeed C>=9 and A>K>=3 imply 3(A+1)<CA-1, so
(A+1)H=(A+1)(q-1)/(CA-1)<q/3. Thus all ten fields are
nonnegative and strictly less than q before q or R has been proved to be
a power. Gstar is positive because AH>0. No field-range guard is unpaid.

## 3. The kernel bootstrap, powers, and actual field masks

Ordinary Horner packing of nonnegative registers gives P>=0. Equations(6)
give

    r=(D0-1)/2+P, r<D0.                                   (10)

Here q>=R>K^2>=9, so D0=q^10 is much larger than81. In particular
r>=(D0-1)/2>=27 and D0<r^2. Thus all four general kernel hypotheses

    D0>=81, r>=27, r<2D0, D0<r^2

hold before any exponent conclusion. The parity-free kernel proves

    U_pell=3^(2r+1), D0 divides U_pell,
    D0 divides binom(2r,r).

Since q is a positive integer and D0=q^10, q must be a power of three.
The positive divisor R of q is therefore also a power of three. Equation(5)
then says R-1 divides q-1, forcing q=R^t for a positive integer t.
The fixed power C divides R, so A=R/C is a power of three as well.

Write D0=3^n. By the direct unit-two mask theorem in
`EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`, Section1, the divisibility and
0<r<D0 force every one of r's n trits to lie in{1,2}, with unit trit2.
Subtracting the all-one word (D0-1)/2 in (10) involves no borrow: P is
a Boolean ternary word with unit trit1. The pre-mask bounds (8),(9) make
the q-Horner blocks actual disjoint fields, so every field in (4) is Boolean.

This is why field bounds cannot merely be omitted from a raw packing
argument. For example, q=81 and a formal first field q+1 with all other
fields zero give a Boolean P=q+1 and a valid native mask index, although
the first field exceeds q. That is a packing-only alias, not a solution of
the tag sources. The retained length comparison excludes it here through
the independent bounds above.

## 4. Exact guard equivalence and the fixed unit digit

The original ten fields do not include a field with a uniform unit trit1.
In particular G=Q+AH has unit trit equal to the first selector. For
beta=2 and u=0, all four length-two binary words halt after one step.
Across these four valid source rows, each original field has unit zero
in at least one case. Thus simply putting G first was not a general-input
solution, even when restricting attention to actual halting inputs.

We now prove that replacing G by Gstar preserves the conditional system.
The typed S0,S1 sum to H without ternary carries, hence are complementary
subsets of row heads. The word AH is Boolean and its occupied position
in each row differs from the head because A>Linit>=3. Thus AH+S0 is
Boolean. Since Q is Boolean, Q+(AH+S0) has trits at most2 and creates
no ternary carries. Booleanity of Gstar forces these supports disjoint.
In particular the original G=Q+AH is Boolean. All other masks and
equations of the31 predecessor have now been restored, proving soundness
for eventual halting from the specified word.

Conversely, in every solution of the predecessor the projector theorem
says Q is zero in every inactive S0 row and is the initial interval in
every active row. Hence Q and S0 are disjoint; AH is disjoint from each.
Therefore Gstar is Boolean and less than q. At the first genuine source,
the length is at least beta>=1. Its interval's unit trit is1 exactly when
the selector is1. As S0 has unit1 exactly when that selector is0,

    Gstar mod3 = Q_unit+S0_unit = 1.                       (11)

This conclusion applies also to admitted certificates with a suffix after
the first real halt. It assumes no fixed initial selector.

## 5. Complete positive converse and parity

Given an actual finite halt, choose the canonical31 witness, widening A
as in that theorem. Replace each of its nine zero-capable source words
and Nfinal by the positive coordinate F_X=X+1. Every supplied coordinate
outside the Pell subsystem is now positive. The proof in Section4 supplies
the Boolean Gstar and its unit trit1.

Pack the ten fields, put D0=q^10 and r=P+(D0-1)/2. Their trits show
P<=(D0-1)/2. This inequality is strict: the field S0<=H is strictly
less than (q-1)/2 because R>3, so its entire block cannot be all ones.
Hence betaP=D0-r is positive. The native r has unit trit2 and all other
trits1 or2, giving valuation v3(binomial(2r,r))=log_3(D0).

The general44-operation kernel therefore supplies its seventeen positive
auxiliaries for this exact D0,r, without imposing a parity. All outer
coordinates, including both encoded endpoints, are preserved. This proves
the complete positive existential equivalence to halting under the stated
encoded-input contract. No enormous Pell witness is required to be computed
for the existence proof.

The parity-free choice is substantive for this order: the canonical tests
contain598 even indices and346 odd indices. This finite fact is not a lower
bound against other parity arrangements. A separately stipulated fixed
first selector would allow S0 or S1 as the first original field and avoid
the one Gstar addition; that stronger input contract is not assumed here.

## 6. Exact ledger and verification scope

| Component | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Frozen31 tag component | 14 | 17 | 31 |
| Gstar addition | 0 | 1 | 1 |
| Row geometry | 2 | 2 | 4 |
| q^10 power chain | 4 | 0 | 4 |
| Ten-field raw Horner packing | 9 | 9 | 18 |
| Shared index and strict upper bound | 0 | 3 | 3 |
| Parity-free Pell kernel | 26 | 18 | 44 |
| Nine word adapters and terminal adapter | 0 | 10 | 10 |
| **Total** | **55** | **60** | **115** |

With nonnegative coordinates admitted, omit the ten adapters and obtain105.
The mask/power/index/kernel part alone is69; the general first-unit repair
is the separately shown one addition. If a fixed initial selector is an
additional input promise, the unadapted ledger is104. Alternatively a fixed
low native trit can be inserted for arbitrary input: use scale3q^10 and
tr1=3q^10+6P+2. That requires two extra operations relative to the provisional
unit-unchecked ledger, giving106 before adapters. Gstar improves that
unconditional unit treatment by one operation.

`../verification/explore_single_projector_tag_packing.py` constructs the
complete DAG and independently expands every outer source polynomial after
the ten positive substitutions. It checks all eleven kernel sources and
the exact norm-source correction, giving25 source comparisons. Its63
pre-power geometry cases include61 nonpowers q; these are rational-bound
tests, explicitly not claimed full system solutions.

Fresh canonical construction checks944 halting histories and2,318 source
rows, both initial selectors,1,711 zero-valued word coordinates, and746
zero terminal contents. Each case evaluates all14 actual outer comparisons,
all ten fields, the actual packed r, its exact valuation and the kernel
preconditions. A three-row certificate with a genuine halt after its first
row is checked separately. The428 runs still active after20 steps remain
unclassified. The seventeen enormous Pell auxiliaries are not materialized;
their existence is the cited general kernel theorem. The checker and proof
do not claim a universal startup, raw numerical-input conversion, optimal
adapter cost, or a new universal operation frontier.
