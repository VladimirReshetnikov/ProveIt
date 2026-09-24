# An extra forbidden digit enforces the program width: 114 operations

The complete packed-bound115 system can enforce its own fixed program
width. Add one sufficiently high, unused ternary digit to its existing
forbidden-position mask, then delete the equation R=Rmin*zR. The added
digit changes a fixed coefficient in an existing product; it does not
add an instruction. The result is **114 operations:55 products and59
additions/subtractions**, with **42 positive unknowns and30 equations**.

The exact source/checker and receipt are
`../verification/explore_intrinsic_program_width.py/.json`. The unchanged
predecessor is `EXPLORATION_PACKED_BOUND_SERIAL_COMPOSITION.md`. Its
complete raw-counter, cyclic routing, and positive Pell proofs are used
below only after their required bounds have been established.

This is a further alternative universal family, above the existing
universal bound of90. The representation changes some packed coordinates;
the proof gives equality of the accepted input predicates, not a claim
that all old witnesses stay numerically unchanged.

## 1. Fixed mask and exact source change

Use the same finite cyclic-entry graph, state codes, transition numeral
K, support S, multiplier g, initial singleton I, and output weights
hs,hz as115. Let Z0 be its forbidden-position numeral, comprising the
count-marker high positions and the two selected label positions.
Its ternary digits are0 or1, and Z0>hs+hz. Choose a fixed power

    E=3^e>max(KS,gS,6(hs+hz),Z0,Rmin_old,9),
    Zstar=Z0+E.                                  (1)

Here Rmin_old is only a convenient fixed number used to choose e.
It will not be imposed by an equation. Because E>Z0, its position
does not coincide with an old forbidden digit. Because E>KS, it is
above the entire coefficient range of every single canonical ROM row.
Thus Zstar is also a Boolean ternary numeral.

Replace the source equality

    TV=V+Z0 H

by

    TV=V+Zstar H.                                (2)

Delete the positive supplied coordinate zR and the equation
R=Rmin_old*zR. All other sources remain, including

    q=2J+1, q=Wv, W=R^3, H(R-1)=2J,
    NC=J+C, NV=J+V, NTC=J+TC, NTV=J+TV,
    C+J=SH+TC,
    r=P, r+beta=q^12.

The order of P's twelve fields is unchanged:

    FKplus,G0,F0,G1,F1,FKminus,FZ,FZbar,NC,NV,NTC,NTV.

The complementary top source, all raw-counter equations, cyclic routing
equation, and all ten source comparisons of the43-operation fixed-sign
kernel are unchanged. The checker independently expands each retained
source. Relative to115, only(2) changes among retained polynomials, by
the term -EH; the width source and its one product are deleted. The
acyclic auxiliary-norm correction remains at the same index.

## 2. The last supplied field bounds the width before the kernel

At this stage every assertion is about positive integer equations.
There has been no power recovery or digit interpretation. Since J>0,
the equation q=2J+1 gives q>=3. Positivity of every packed field and
beta yields

    q^11<P=r<q^12.

In particular the highest supplied field obeys

    NTV*q^11<P<q^12, hence NTV<q.

This bound is on NTV itself, even if lower supplied fields would carry
into its normalized chunk. The adapter NTV=J+TV therefore gives

    0<V<TV<=J.

Using(2), V>0 and H>0 gives the decisive bound

    Zstar H<J,
    R-1=2J/H>2Zstar.                            (3)

The quotient in this proof is only algebraic reasoning from the
already supplied equality H(R-1)=2J; it is not a free arithmetic
instruction in the schedule.

Equation(3) implies R>=9, R>KS, R>gS, R>2S+1, and R>Zstar.
The last two support inequalities also use g>=1 and(1). The equations
q=Wv and W=R^3 now give q>=R^3>=729 and H<=J/4. Thus every width
bound used to recover the raw-counter fields in115 is available before
its kernel. There is no circular requirement of the form R>12Zstar:
that stronger bound is neither assumed nor needed.

## 3. Kernel, raw counters and the two zero flags

The direct packed bound gives the complete general-scale hypotheses

    D0=q^12>=81, r=P>=27, r<D0<2D0, D0<r^2,

where the last inequality follows from P>q^11 and q>1. The unchanged
kernel recovers q as a power of three and the required divisibility
of the central binomial coefficient. Since P<D0, its direct unit-two
mask makes every normalized q-chunk native and the unit trit two.

The raw-field proof of115 now applies with exactly its stated integer
bounds. For clarity, its order is as follows. The first sign field has
no overflow and is at least J. The exact time equation then gives
A=F0+F1-2J<J and F0,F1<3J. The complementary top source initially
gives only T<(R+3)J/6. This weak bound is enough to put the two
guard/base carry pairs below R,1,R,1 respectively. Together with
FKminus<=J+H, it proves zero carry into FZ.

The zero-pair sum is2J+H. A putative overflow of FZ would leave a
remainder below J, so FZ is native and at least J. Its complementary
field FZbar is then below q and is also native. Only now does

    6(J-T)=(R-3)(FZbar-J)

give T<=J. Repeating the adjacent guard/base argument excludes all
remaining carries in the low six fields. All eight raw-counter and
zero fields are their own normalized chunks. This reasoning neither
uses a program aggregate bound nor presumes Booleanity of C.

Write Kplus=FKplus-J and D=FZbar-J. They are Boolean head subsets,
with0<=Kplus,D<=H. The raw-counter equations therefore represent
ordinary nonnegative signed numerical histories with initial values
[2x,0,0], zero target, exact source-zero guards, and first sign plus.
The even initial values and zero endpoints enforce complete even banks,
as in the predecessor. The true zero request remains Z=H-D.

## 4. Decode the program without its former explicit width equation

The strict bound V<TV<=J already holds before typing. With the now
typed flags, the existing routing-output expression satisfies

    O=V+hs Kplus+hz D
      <=V+(hs+hz)H
       <V+Zstar H=TV<=J<q.                     (4)

This is stronger than the looser115 bound O<7J/6. It does not require
R to exceed a multiple of the new Zstar.

The fixed table has K>=3 and S>=I>=1. From(3),(1), gI<R and g<R,
so RK-g>gI+R>0. The cyclic routing equality is

    (RK-g)C=gI(q-1)+RO.

Using(4) proves C<q. Consequently NC=J+C<q+J. There is no incoming
carry after the eight recovered fields; a native remainder excludes
NC>=q. Thus NC is native and C is Boolean. Likewise NV=J+V<q is
native without carrying. Finally

    NTC=J+TC=NC+J-SH<q+J

has no overflow, and NTV<q also has no incoming carry. All twelve
supplied fields have now been recovered.

It follows that C,V,TC,TV are Boolean words below q. The complement
support equation restricts C to SH. The width bound R>KS makes
all fixed-ROM coefficients stay within their intended time rows; the
unchanged Sidon and marker proofs apply. The new mask still contains
every old forbidden position, so V is zero at all required count,
successor-label and zero-label positions. Its additional forbidden
position can only impose one more constraint. The decoded sources
therefore form exactly one state per row, follow only permitted
transitions, and have the specified signs and true source-zero tests.

The same cyclic first-return argument gives acceptance of the original
raw input. It is not necessary to recover an old merged slack before
this conclusion: every raw-counter and routing hypothesis used above
has been proved directly.

## 5. Positive converse and the fresh forbidden position

Fix an admissible finite accepting history in the unchanged program.
Choose R to be a power of three, as large as necessary so that

    R>2Zstar, R>2x,
    every numerical source value is less than R/3.

There is no longer a supplied multiple-of-Rmin requirement. Powers
of three are unbounded, so these finitely many inequalities can all
hold. Form W=R^3, q=R^u and H=1+R+...+R^(u-1), where u is the
history's positive number of serial blocks. The accepting compiler's
duration is a multiple of six, so q=W^t with positive v=q/W.

Construct the same two numerical tracks, true-zero word and its
complement, guards, and source-state word C. Put

    V=KC-g Next-hs Kplus-hz D,
    TC=C+J-SH, TV=V+Zstar H,
    NC=J+C, NV=J+V, NTC=J+TC, NTV=J+TV.

Each canonical ROM row has positive Boolean junk v_i, including the
count-marker unit bit, and v_i<KS<E. The old forbidden positions
are disjoint from that junk. The added bit E is above both v_i and
Z0, so v_i+Zstar is still Boolean. Moreover

    v_i+Zstar<KS+Zstar<2Zstar<R.

There is no inter-row carry. Consequently TV is Boolean and below q,
just as C,V,TC are. TestC is positive because R>2S+1; V and TestV
are positive by the count marker and the nonempty forbidden mask.
All other supplied raw and native fields have the predecessor's
positive constructions. The input slack R-2x is positive.

Thus P has exactly twelve native q-chunks and is below q^12. Set
beta=q^12-P>0. The first sign is plus, so P has unit digit two.
All counter pairs have even total parity; the program native fields
have sum

    NC+NV+NTC+NTV=2(C+V)+5J+(Zstar-S)H.

Both J and H are even for the accepting duration, so this sum is even
regardless of the newly added mask bit. Hence P is even. The same
complete fixed-sign43 positive converse constructs every remaining
Pell coordinate from the new P and D0. No old enormous Pell coordinate
is assumed to survive the change in packing.

For any recursively enumerable set, its fixed ordinary-input compiler
supplies the finite graph. Choosing e by(1) only changes fixed numerals
depending on that graph, never on x. The exact resulting114-operation
system has positive witnesses precisely for the members of that set.
The operation x+x is still counted. The established universal90 family
remains the smaller verified construction.

## 6. Count and evidence boundary

The product Z0*H becomes Zstar*H at no change in count. The sole
deleted instruction is Rmin*zR, with its supplied zR and comparison.
Thus115-1=114=55M+59A, with42 unknowns and30 equations. The checker
expands all30 sources against all114 primitives, including the
unchanged auxiliary correction. It tests the width implication on
ordinary positive integer tuples, including non-power widths, and
checks the extra forbidden digit on every edge of the fixed example.

Its complete canonical examples construct the new TestV, native field,
packed word, slack and exact central-binomial valuation. They verify
all20 outer equations and every positive-kernel hypothesis. The
enormous Pell coordinates are supplied by the full converse proof,
not numerically instantiated. Finite regressions are separate evidence
from the general width, decoding and necessity arguments above.

The fresh receipt contains28,672 positive width tuples, including27,922
whose widths are not powers of three, and all eight fixed-ROM edges.
The added position is e=1,507; the two canonical examples choose a
width of1,508 ternary digits and have12 and18 serial blocks. They check
all20 outer source residuals and exact valuations217,152 and325,728,
respectively. Their packed words have344,178 and516,267 bits. These are
new packed words under the enlarged mask, rather than inherited115
canonical receipts.
