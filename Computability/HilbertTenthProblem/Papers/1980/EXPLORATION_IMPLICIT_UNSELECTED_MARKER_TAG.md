# Recovering the unselected marker for appendants of length at least two

Review status: author and two independent complete proof/source reviews and
fresh verification runs passed without findings. The construction and
arithmetic are frozen. The frozen 111 predecessor is unchanged.

For a fixed binary tag program whose nonzero appendant has length **a>=2**,
this successor to `EXPLORATION_IMPLICIT_PREFIX_COMPLEMENT_TAG.md` costs
**110 operations = 55 multiplications + 55 additions/subtractions**, with
**34 positive existential unknowns and 21 equations**. It preserves the
complete positive encoded-word halting equivalence under that explicit
restriction. The deletion number beta may be any positive integer. The
result retains the specified Boolean ternary input encoding and makes no
ordinary numerical-input or universal operation claim.

## 1. Delete an adapter and derive the other marker

The111 schedule supplies positive F_M0, computes M0=F_M0-1, and compares
lengthsum=M0+M1 with positive L. Remove F_M0, its adapter and this comparison.
After the existing output M1=2Q+S1 has been computed, instead compute

    M0=L-M1.                                                (1)

This removes two additions/subtractions and adds one, with one fewer
unknown and one fewer equation. The field order remains exactly

    Gstar, Q, S0, S1, M0, M1, Ebar, E, Nbar, N.              (2)

The18-operation Horner packing, power products, packed index and44-operation
parity-free kernel are unchanged. M0 is now a potentially signed register,
and its nonnegativity must be proved; it is not a supplied domain.

Use the111 constants K=3^beta, Kh=K/3, B=3^(a-1), U and C. The present
restriction gives B>=3, which is essential to the pre-mask argument below.
Keep positive Nsum and the definitions

    M1=2Q+S1, S0=H-S1, Ebar=cH-E,
    Nbar=Nsum-N, Gstar=Q+AH+S0.

Here Q,S1,N,E,Nfinal remain positive supplied coordinates minus one, so
they are nonnegative before using the kernel. The ten outer equations are
precisely the eleven equations listed in111 with M0+M1=L removed and
M0 replaced by(1). In particular the length source becomes

    R[L+(B-1)M1]=Kh(L-Linit+q Lfinal).                       (3)

The remaining eleven equations are the identical generic kernel equations
with D0=q^10. All34 supplied existential coordinates remain strictly positive.

## 2. Bounds before any mask conclusion

The initial and geometry sources still give

    A>Linit>=K, R=CA>K^2, q>=R,
    H=(q-1)/(R-1)>0, 0<Lfinal<K.

Since L>0, M1>=0 and B-1>=2, equation(3) implies

    RL<=R[L+(B-1)M1]<Kh(L+Kq),
    L<K^2*q/(3R-K)<q/2.                                   (4)

The same equation, now bounding the selected-marker term separately, gives

    R(B-1)M1<Kh(K+1/2)q,
    M1<K(K+1/2)q/[3R(B-1)]<7q/36<q/2.                    (5)

The second strict bound uses R>K^2, B-1>=2 and K>=3. Therefore

    -q/2<M0=L-M1<q/2.                                     (6)

The nonnegative summands in M1=2Q+S1 also give Q<q/4 and S1<q/2.
Consequently the earlier signed bounds remain valid:

    -q/2<S0<=H<q,
    -q/2<Gstar<q/4+q/3<q.                                (7)

No marker mask, first-selector promise, or recovered sign of M0 has been
used. The retained containment equation gives 0<Nsum<L/2<q/4.

## 3. Positive packing despite three potentially signed fields

Although M0 can be negative, the combined slots4 and5 are strictly positive:

    M0+qM1=L+(q-1)M1>0.                                  (8)

Let Plo6 be the formal packing of the first six fields in(2). Grouping
the last two of these as in(8), only Gstar and S0 contribute possible
negative terms, at positions0 and2. Thus

    Plo6>-(q+q^3)/2>-q^3.

Exactly as in111, the remaining combined pairs satisfy

    TE=Ebar+qE=cH+(q-1)E>=0,
    TN=Nbar+qN=Nsum+(q-1)N>=1,
    P=Plo6+q^6 TE+q^8 TN>q^8-q^3>0.                       (9)

The index equation 2r+1=q^10+2P and positive bound r+betaP=q^10 therefore
give all hypotheses of the reviewed44-operation kernel before typing:
D0>=81, r>=27, r<2D0 and D0<r^2. It forces q and R to be powers of
three, q=R^t, and P to be a Boolean ternary word with unit trit1. The
positive kernel bootstrap has not depended on an assumed nonnegative M0.

## 4. Low-block recovery restores the entire111 source

Set J=(q-1)/2 as a proof abbreviation. The proof from111 first decodes
Gstar,Q,S0,S1 in order. A negative Gstar or S0 would, by(7), normalize
to a q-chunk greater than J; that is impossible for a Boolean ternary
block. The intervening nonnegative fields are already less than q and
introduce no carry or borrow.

At slot4 the same argument now applies to M0. Bound(6) makes a negative
value normalize to q+M0>q/2>J. Hence M0>=0. By(5)--(6), M0 and M1
are the literal next two Boolean blocks, with no outgoing carry. Thus

    0<=Plo6<q^6, M0>=0, M0+M1=L.                          (10)

This recovers all preconditions used at the corresponding point of111.
Its proof of N<=J now applies to TE>=0 and P>=q^8 TN. Since M0 is
nonnegative again, its stronger append bound

    R B M1<=R(M0+B M1)<Kh(K+1/2)q

also applies unchanged. Therefore the original111 content argument yields
E<13q/36+1/6<q/2, then recovers nonnegative Boolean Ebar and E, and
finally recovers Nbar. A weaker bound using only B-1 is unnecessary after
this decoding step. All ten fields and their original tag meanings follow.

Equivalently, one may restore F_M0=M0+1 as soon as(10) is proved. Every
source equation and positive coordinate of111 then holds, including its
unchanged packed/kernel equations. The complete111 theorem supplies the
remaining decoding and first-halt conclusion without any additional
condition. This observation also makes the positive correspondence exact.

## 5. Unique positive extension and unchanged index

Every110 solution has the unique positive former coordinate

    F_M0=M0+1=L-2F_Q-F_S1+4>0.                            (11)

All other coordinates and computed values are unchanged. Conversely, the
111 length comparison implies(1), so forgetting its positive F_M0 gives
a110 solution. The source domains used in this correspondence include the
fixed a>=2 contract throughout.

The packed word P, r, betaP, scale and all seventeen Pell auxiliaries are
identical in the two solutions. Unlike the preceding prefix-field swap,
this step needs no repacking or fresh kernel witnesses. Canonical histories
with M0=0 are valid: their restored F_M0 is one. The same first-halt scope,
including admitted formal continuations after a genuine halt, is preserved.

## 6. The one-symbol appendant case is separate

When a=1, each source step deletes beta symbols and appends exactly one,
independent of the selector. For beta>=2 the length decreases by beta-1
at each step, so every valid initial word of length at least beta eventually
becomes short. For beta=1 the length is constant and no such initial word
halts. These are elementary semantic classifications.

They do not establish that this110 source system is sound when B=1, and
the theorem does not assert that extension. No case-disjunction arithmetic,
input compiler or universal startup is being hidden in the110 count.

## 7. Complete source check and fresh finite evidence

`../verification/explore_implicit_unselected_marker_tag.py` constructs all
110 instructions, ten outer sources and eleven kernel sources. Under(11)
the deleted length source is identically zero. Every retained source is
checked by exact expansion, including the norm-source correction at combined
index18. The packed polynomial and index expression are independently
checked to agree with111 exactly under the same substitution.

The bounded normalization check covers16,606 marker pairs, rejecting8,124
negative markers and accepting708 Boolean pairs. It separately checks
45 exact rational bounds underlying(5). The tested pair ranges enlarge the
actual source ranges; they are normalization tests, not asserted complete
tag source tuples.

Fresh canonical construction for a=2,3 covers776 halting histories and
2,006 source rows. Every example evaluates ten new and eleven restored
outer comparisons, all ten masks and the exact index valuation. All776
indices are preserved;514 are even and262 odd. There are48 zero M0 words.
The three-formal-row example with a true halt after one step is retained.
The400 runs reaching the finite cutoff remain unclassified. A separate
one-symbol semantic check covers392 decreasing-length halts and28
constant-length nonhalts; those runs are not counted as110 source cases.

The enormous Pell auxiliaries are not materialized. Their existence and
exact preservation follow from111 and(11). Neither optimality nor a change
to the separate universal numerical-input frontier is claimed.
