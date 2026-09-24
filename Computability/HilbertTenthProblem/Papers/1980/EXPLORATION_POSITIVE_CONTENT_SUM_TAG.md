# One fewer positivity operation through the highest content pair

Review status: author verification and independent root and binary complete
proof/source reviews and fresh runs passed. The review correction to the
weak packing bound in Section3 is incorporated; no findings remain. The
mathematical construction and arithmetic are frozen.

This is a separate successor to the positive encoded-word115 certificate
in `EXPLORATION_SINGLE_PROJECTOR_TAG_PACKING.md`. It costs **114 operations
=55 multiplications+59 additions/subtractions**, with the same **38 positive
existential unknowns and25 equations**. It preserves the complete halting
equivalence for the specified encoded binary input word. It does not supply
ordinary numerical-input conversion, a universal startup, or a new universal
operation bound. The115 predecessor is unchanged.

## 1. Coordinate and packing change

Use exactly the fixed program, input contract and notation of115. Replace
the positive supplied coordinate F_Nbar by a positive supplied coordinate
Nsum. Delete the adapter Nbar=F_Nbar-1 and the addition
content_sum=N+Nbar. Replace uses of content_sum by Nsum and compute

    Nbar=Nsum-N.                                            (1)

The containment comparison is now simply

    2Nsum+H=L.                                             (2)

N still has its paid adapter N=F_N-1>=0. The other eight adapters, including
the terminal adapter, are retained. At this point Nbar is a signed computed
register; its nonnegativity is not a premise. Removing two additions/
subtractions and adding(1) saves exactly one operation.

Change the ten-field packing order to

    Gstar,Q,S0,S1,M0,M1,E,Ebar,Nbar,N.                       (3)

All other sources, geometry, Gstar=Q+AH+S0, scale D0=q^10, index relation
2r+1=D0+2P, upper bound r+betaP=D0, and the parity-free44 kernel are retained.
Horner packing still costs18 operations. The complete new DAG and all25
source polynomials are in `../verification/explore_positive_content_sum_tag.py`.

The new packing is not the old numerical P. Its index r and positive Pell
witnesses must be rebuilt. No identity of the old and new packed witnesses
is assumed.

## 2. Bounds that survive before typing

The initial and length equations are unchanged. Positivity still gives

    R=CA>K^2, q>=R, H=(q-1)/(R-1)>0,
    L<K^2*q/(3R-K)<q/2.                                   (4)

Hence M0,M1<q/2 and Q<q/4. Equation(2), with supplied Nsum>0,
gives Nsum<L/2<q/4. The old arguments also give

    S0,S1<=H<q, E,Ebar<=cH<q,
    0<Gstar<=Q+(A+1)H<q/4+q/3<q.                          (5)

These bounds apply to the first eight fields of(3). They do not assume
anything about the sign of Nbar or impose a premature bound on N.

Let Plo be the ordinary packing of those first eight fields. They are
nonnegative and less than q, so

    0<=Plo<q^8.

The highest pair has the exact identity

    Nbar+qN=Nsum+(q-1)N=:T>0,                              (6)
    P=Plo+q^8 T>0.

Positivity of the entire packing thus survives even when the low member
Nbar of this pair is negative. With 2r+1=D0+2P and r<D0, the115 kernel
bootstrap is unchanged: D0>=81, r>=27, r<2D0 and D0<r^2 hold before
power or digit decoding. It proves q is a power of three, R is a power
of three, q=R^t, and P is a Boolean ternary word with unit trit1.

## 3. The highest pair rules out the negative complement

Now q is odd. Write J=(q-1)/2 only as mathematical notation; no J is
computed by the schedule. Since r<D0,

    P<=(q^10-1)/2.

Together with Plo>=0 and(6), this implies

    2T<q^2, hence T<=(q^2-1)/2.                            (7)

As Nsum>0, equations(6),(7) force N<=J. Indeed, if N>=J+1,
then (q-1)N>=(q^2-1)/2 and adding Nsum violates(7).

Suppose Nbar=Nsum-N<0. Then -q<Nbar<0, and the two normalized q-chunks
of the highest pair are exactly

    q+Nbar, N-1.

The low chunk satisfies

    q+Nbar=q+Nsum-N>q-N>=q-J=J+1.                          (8)

But every Boolean ternary word below q is at most J. Equation(8)
contradicts the Booleanity of P. The already bounded Plo lies below q^8,
so no carry from it alters this argument. Therefore Nbar>=0.

It follows that N<=Nsum<q/4 and Nbar<=Nsum<q/4. Both highest q-chunks
are now the original computed Nbar and N themselves. Thus all ten fields
in(3) have the same individual Boolean meaning as in115. In particular the
old guard is restored from Gstar, and all31 tag equations and masks hold.
The predecessor's first-halt proof establishes soundness for the same
specified encoded word, including certificates with a suffix after its
first genuine halt.

## 4. Complete positive converse and the witness distinction

Take a genuine finite halt and the canonical115 outer words. Their sum

    Nsum=N+Nbar

is strictly positive: at the first source row its value is the interval
(Linit-1)/2>=1. Supply that sum in place of F_Nbar. Every other supplied
outer coordinate is positive as before, and(1) reconstructs the exact old
nonnegative complement. Conversely, after the new mask proof one recovers
the positive former coordinate F_Nbar=Nbar+1. Thus no possible zero
complement is lost; the new regression includes15 such canonical histories.

Repack these Boolean words in order(3). Gstar remains the first field and
has unit trit1 for either initial selector. Since S0<=H<(q-1)/2, at least
one packed trit is zero, so P<(q^10-1)/2. Put r=P+(q^10-1)/2 and
betaP=q^10-r>0. The native r has unit2, all other trits1 or2, and exact
valuation log_3(q^10). The general44 kernel supplies all seventeen positive
auxiliaries for this new index and scale, without a parity restriction.

This proves the complete positive encoded-input equivalence. It preserves
the outer decoded history and endpoints, but not the old packed index or
the old Pell auxiliary values. It is not asserted to be a literal bijection
of all old and new full Pell witness tuples.

## 5. Count and exact evidence

The115 source performed three operations for this local group:

    Nbar=F_Nbar-1, content_sum=N+Nbar,
    twice_content=2*content_sum.

The new source performs two:

    Nbar=Nsum-N, twice_content=2*Nsum.

Every other operation count, including the18-step packing, is unchanged.
The result is114=55M+59A,38 positive unknowns,14 outer and11 kernel
equations. All13 nonpacking outer source polynomials are literal copies
of the115 polynomials under

    F_Nbar=Nsum-F_N+2.

The packing source is independently expanded for its new order. The checker
also verifies all eleven kernel sources and the existing norm-source
correction at combined index22.

The finite highest-pair check covers74,664 pairs, including55,677 negative
formal complements rejected by(8), and1,089 accepted Boolean pairs.
It separately records540 pairs rejected by the packing upper bound. These
are tests of the stated pair ranges, not claimed complete history solutions.

Fresh canonical construction covers944 actual halts and2,318 source rows.
For every case it evaluates all14 new outer comparisons, ten field masks,
the exact native index and valuation. It then restores the old positive
coordinate and repacks in the old order, checking all14 old outer comparisons
and that old index's valuation too. All944 packing indices change; the parity
counts remain598 even and346 odd. A genuine one-step halt with three formal
source rows is also checked. The428 cutoff runs remain unclassified.

The huge positive Pell auxiliaries are justified by the general kernel
converse and are not materialized. No frozen predecessor is edited, and no
claim of optimal adapter cost or universal raw-input arithmetic is made.
