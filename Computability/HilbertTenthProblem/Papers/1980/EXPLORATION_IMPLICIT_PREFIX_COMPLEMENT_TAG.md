# Recovering the prefix complement after decoding the content bound

Review status: author verification and independent root, binary and algebra
complete proof/source reviews and fresh runs passed without findings.
Mathematical construction and arithmetic are frozen. The frozen112
predecessor is unchanged.

This successor to `EXPLORATION_DERIVED_SELECTED_MARKER_TAG.md` costs
**111 operations = 55 multiplications + 56 additions/subtractions**, with
**35 positive existential unknowns and 22 equations**. It preserves complete
positive encoded-word halting equivalence for every deletion number beta>=1
and every nonempty binary appendant. The input is still a specified Boolean
ternary encoding of a binary word. This is neither an ordinary numerical
input compiler nor a universal operation bound.

## 1. Exact change and retained source equations

Delete the positive coordinate F_Ebar, its adapter Ebar=F_Ebar-1, and the
comparison computed by prefix_sum=E+Ebar against prefix_scale=cH. Reuse the
already computed prefix_scale and instead compute

    Ebar=cH-E.                                                  (1)

This removes two additions/subtractions and introduces one. Move the prefix
complement before its partner in the ten-field order:

    Gstar, Q, S0, S1, M0, M1, Ebar, E, Nbar, N.                 (2)

The ordinary18-operation Horner packing is unchanged in cost. The order
change alters the packed value and index, so the positive kernel witnesses
will be constructed afresh; they are not claimed to be preserved.

Use the predecessor constants

    K=3^beta, Kh=K/3, Af=3^a, B=Af/3, c=(Kh-1)/2,

where a>=1, and let U be the ternary value of the fixed binary appendant.
Thus B>=1 and 0<=U<3B/2. The fixed power of three C satisfies
C>max(K,Af,2U+3). The designated parameters are Linit=3^ell and Ninit,
where ell>=beta and Ninit is a Boolean ternary word below Linit. In
particular 0<=Ninit<Linit/2. The raw coordinates Q,S1,M0,N,E,Nfinal are
the corresponding positive supplied coordinates minus one. Retain positive
supplied Nsum and compute

    M1=2Q+S1, S0=H-S1, Nbar=Nsum-N, Gstar=Q+AH+S0.

These formulas and(1) define registers, not additional comparisons. The
eleven outer source equations are exactly

    CA=R,
    M0+M1=L,
    2Nsum+H=L,
    R(N-3E-S1+U M1)=K(N-Ninit+q Nfinal),
    R(M0+B M1)=Kh(L-Linit+q Lfinal),
    Linit+alphaI=A,
    Lfinal+alphaH=K,
    H(R-1)=q-1,
    Rv=q,
    2r+1=q^10+2P,
    r+betaP=q^10,                                             (3)

with P the packing(2). All supplied existential coordinates are strictly
positive; only the displayed raw registers can be zero or signed. Append
the unchanged eleven source equations of the44-operation kernel in
`EXPLORATION_PARITY_FREE_PELL_KERNEL.md`, with D0=q^10. The complete DAG
and all22 source residuals are in the companion checker and receipt.

## 2. Pre-power bounds and positivity of the signed packing

The retained initial and geometry equations imply

    A>Linit>=K, R=CA>K^2, q>=R,
    H=(q-1)/(R-1)>0.

Since B>=1, M0+M1=L and M0,M1>=0, the length equation and Lfinal<K give

    (R-Kh)L<Kh*K*q,
    L<K^2*q/(3R-K)<q/2,
    0<Nsum=(L-H)/2<L/2<q/4.                                 (4)

Consequently M0,M1<q/2, Q<q/4 and S1<q/2. As in the113 proof,

    -q/2<S0<=H<q,
    -q/2<Gstar<q/4+q/3<q.                                  (5)

The guard upper bound follows from (A+1)H<q/3; for example
3(A+1)<CA-1=R-1 because C>=9 and A>K>=3. No bound on E or sign of
Ebar is used here.

Let Plo6 be the formal packing of the first six entries of(2). Only
positions0 and2 can be negative, so

    Plo6>-(q+q^3)/2>-q^3.                                   (6)

The two remaining pairs have the positive or nonnegative combined values

    TE=Ebar+qE=cH+(q-1)E>=0,
    TN=Nbar+qN=Nsum+(q-1)N>=1.

It follows before any mask conclusion that

    P=Plo6+q^6 TE+q^8 TN>q^8-q^3>0.                         (7)

The last two equations of(3), with D0=q^10, now give the same kernel
hypotheses as115: D0>=81, r>=27, r<2D0 and D0<r^2. The reviewed
general44-operation theorem applies without a parity restriction. It
forces q to be a power of three. Since R divides q and R-1 divides q-1,
R is a power of three and q=R^t for an integer t>=1. The direct native
mask conclusion says that P is a Boolean ternary word with unit trit1.
In particular, with J=(q-1)/2 used only as a proof abbreviation,

    P<=(q^10-1)/2.                                         (8)

The weak inequality in(8) is sufficient throughout the soundness proof.

## 3. Decode the first six blocks before bounding the high fields

The higher two combined pairs are multiples of q^6 and cannot change any
of the first six q-chunks. If Gstar were negative, (5) would make its
normalized first chunk q+Gstar>q/2>J, impossible for a Boolean ternary
word below q. Therefore Gstar>=0, and it is the actual first block.
Q is nonnegative and less than q, so its block is also literal. The same
argument excludes S0<0 at the next block. The remaining S1,M0,M1 are
already nonnegative and less than q. Thus all first six fields are Boolean
and their actual packing satisfies

    0<=Plo6<q^6.                                           (9)

This reasoning neither assumes Ebar>=0 nor uses an unsigned interpretation
of the final content pair. Because TE>=0, equations(7)--(9) imply

    q^8 TN<=P<=(q^10-1)/2,
    2TN<q^2,
    TN<=(q^2-1)/2.

Since Nsum is positive and N is nonnegative, TN=Nsum+(q-1)N then forces

    N<=J.                                                  (10)

Indeed N>=J+1 would already give TN>=(q-1)(J+1)+1=(q^2+1)/2.

## 4. The content equation bounds E without using its complement

Rearrange the content source, using Nfinal>=0 and S1>=0:

    3E<=(1-K/R)N+U M1+K Ninit/R.                           (11)

The nonnegative M0 and length source give the strict bound

    R B M1<=R(M0+B M1)
             =Kh(L-Linit+q Lfinal)
             <Kh(K+1/2)q.

Since U<3B/2 and R>K^2,

    U M1<K(K+1/2)q/(2R)<7q/12.                            (12)

The last comparison uses K>=3. The valid input and A>Linit also give

    K Ninit/R<K/(2C)<1/2.                                 (13)

Combining(10)--(13), and (1-K/R)N<q/2, proves

    E<13q/36+1/6<q/2.                                    (14)

The final inequality holds for q>=3. All quantities used in this argument
are still ordinary scalar integers; no digitwise prefix equation or
positivity of Ebar has been presumed.

From(1), c>=0, c<R-1 and(14),

    -q/2<Ebar<=cH<q.

The lower six blocks are already literal by(9). A negative Ebar would
therefore normalize at position6 to q+Ebar>J and contradict the mask.
Hence Ebar>=0. Both Ebar and E are less than q and are the actual next
two Boolean blocks. This also covers c=0 and any zero prefix field.

Now the lowest eight blocks are nonnegative and less than q. For the
last pair, N<=J and Nsum>0 give Nbar=Nsum-N>-q/2. Its upper bound
Nbar<=Nsum<q/4 is also available. If Nbar were negative, its normalized
chunk q+Nbar=q+Nsum-N>J would be impossible. Therefore Nbar>=0, and
both final content fields are their actual Boolean blocks. All ten masks
and the deleted prefix equation E+Ebar=cH have been recovered.

## 5. Positive equivalence and a fresh index in the converse

Every new solution has the unique positive former prefix coordinate

    F_Ebar=Ebar+1=cH-F_E+2>0.

The recovered fields satisfy the full112 outer tag equations and masks,
so its first-halt proof applies, including the already admitted possibility
of formal rows after the first genuine short word. The auxiliary comparison
was recovered from sources and the packed mask, not imposed externally.

Conversely, any112 decoded outer solution, in particular every canonical
halting history, satisfies(1). Forget F_Ebar and reorder the two prefix
fields as in(2). The new P is Boolean, retains the same unit trit of
Gstar, and is strictly below (q^10-1)/2: the field S0<=H is strictly
below the full q-repunit J, since R>=9. Set

    r=P+(q^10-1)/2, betaP=q^10-r>0.

The new native index has the required valuation. The general44-operation
converse provides all seventeen positive Pell auxiliaries for either parity
of this new index. Thus complete positive encoded-input existence
equivalence is preserved. This is not a claim of an identity map on the
old Pell witnesses: swapping E and Ebar usually changes P and r.

## 6. Exact source verification and bounded evidence

`../verification/explore_implicit_prefix_complement_tag.py` constructs the
complete111-instruction DAG and independently checks all eleven outer and
eleven kernel source residuals. The formal substitution
F_Ebar=cH-F_E+2 annihilates the removed source; the new packing polynomial
is expanded separately in the changed order. The retained norm-source
correction is checked at combined source index19. Arithmetic counts include
all adapters, geometry, power products, packing, bound and44 kernel
instructions; no new inequality is supplied for free.

The finite prefix normalization check tests33,396 pairs at
q=3,9,27,81,243. It rejects8,303 negative complements and accepts1,364
Boolean pairs, and checks the exact rational bound(14) at all five widths.
Its arbitrary bases range from0 through q-1, a larger range than the actual
cH interface. These are isolated normalization cases, not full tag sources.

Fresh canonical construction checks944 halting histories with2,318 source
rows, all eleven new and twelve restored outer equations, every field and
both old and new exact index valuations. All944 indices change under the
repacking;598 new indices are even and346 odd. There are84 zero prefix
complements, whose former positive coordinate is one. The existing
three-formal-row example with a true halt after one step is retained. The
428 runs reaching the finite exploration cutoff remain unclassified.

Enormous Pell auxiliary values are not materialized. Their existence for
the new index follows from the reviewed general converse with the stated
hypotheses. This result asserts neither optimality nor any improvement to
the separate universal numerical-input frontier.
