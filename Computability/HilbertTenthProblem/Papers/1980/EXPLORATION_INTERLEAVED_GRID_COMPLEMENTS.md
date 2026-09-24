# Six interleaved complement pairs in 102 operations

The complete raw-counter/controller construction can be evaluated in
**102 arithmetic operations: 54 multiplications and 48 additions or
subtractions**, with 35 positive unknowns and 23 equations. This successor
of `EXPLORATION_COMPLEMENTED_COUNTER_GUARDS.md` keeps all twelve semantic
mask fields. It changes their order and complements both program tests.
A paid two-operation width condition establishes the required bounds
before the Pell argument, so a signed program complement is never used
to justify its own width.

The exact checker is `../verification/explore_interleaved_grid_complements.py`,
with its adjacent JSON receipt. This is a reduction of the alternate
universal architecture. The established universal frontier remains90.
The packed index and its Pell coordinates change; the equivalence is
between represented input predicates, not an identity on old witnesses.

## 1. Fixed grid and source equations

Keep the fixed program constants K,S,g,I,hs,hz and its spacing ell from
the predecessor. Thus B0=3^ell exceeds the number of program states,
B0>=9, and every state and table exponent lies on the ell grid.
The cyclic initial and terminal code is I. The fixed compiled prefix
includes a true zero request, as in the preceding universal construction.

Choose a fixed Boolean ternary numeral Zon on that grid. Include every
on-grid position of the old forbidden numeral Zold and add a fresh high
on-grid bit, so that

    Zon > max(Zold, 4S, 8(hs+hz), g(I+1), (K+g)(S+1), 81).       (1)

The new high bit is above every correct fixed row product. Off-grid
forbidden positions will be excluded by the global grid itself. All
these choices are fixed compilation constants; their use in arithmetic
is still counted.

Write J for the old variable Jrep and t for the old positive gap Tgap.
Add one supplied positive unknown z and compute

    hgrid=Zon+z,
    (B0-1)hgrid=R-1.                                           (2)

These are one addition and one multiplication, with a free comparison
to the already computed R-1. The computed hgrid is not an additional
supplied unknown.

Retain the ten positive fixed-sign Pell equations and their variables
from `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`. The thirteen outer
equations, including their shared scale D0=q^12, are

    q=2J+1, q=Wv, W=R^3, H(R-1)=2J,
    Kplus+Kminus=H, Z+D=H,
    (B0-1)(Zon+z)=R-1,
    6t=(R-3)D,
    W(A0+A1+Kplus-Kminus)=A0+A1-2x,
    2x+alphaI=R,
    2r+1=q^12+2P, r+beta=q^12,
    (RK-g)C=gI(2J)+R(V+hs*Kplus+hz*D).                        (3)

Every supplied unknown remains positive. The sole parameter x is positive.
The twelve conceptual mask fields, in their new order, are

    Kplus, Kminus, Z, D,
    t-A0, A0, t-A1, A1,
    SH-C, C, zH-V, V.                                        (4)

The three kinds of computed complements in (4) need not be positive
before decoding; zero is permitted after decoding. Define P as their
base-q concatenation. Equivalently, using the two flag-pair equations,

    X=Kminus+q²[D+q²(A0+q²(A1+q²(C+q²V)))],
    P=(q-1)X+(1+q²)(H+q^4 t)+q^8 H(S+q²z).                  (5)

Every term in the second expression is positive before any mask theorem
is used. No sign assumption on SH-C or zH-V is needed for this fact.

## 2. Exact operation count and source corrections

The predecessor's portion from `program_qV` through `raw_packed` costs
25 operations, including the shared addition q²+1. Replace it as follows:

| Computation | Multiplications | Additions |
|---|---:|---:|
| X, using five Horner steps with q² | 5 | 5 |
| (2J)X | 1 | 0 |
| q²+1 | 0 | 1 |
| (1+q²)(H+q^4 t) | 2 | 1 |
| q^8 H(S+q²z) | 3 | 1 |
| Sum the three terms | 0 | 2 |
| New width condition (2) | 1 | 1 |
| Total | 12 | 11 |

Thus25 operations become23: one multiplication and one addition are
saved. The old four-product power chain q²,q^4,q^6,q^12 becomes the
four-product chain q²,q^4,q^8,q^12. No power is free. All other
instructions remain, giving102=54M+48A.

The checker expands all23 source equations. To state the only new
packing correction, let

    G=q-2J-1, Fsign=Kplus+Kminus-H, Fzero=Z+D-H.

If Pconcept is the literal concatenation (4), the computed register is

    Pcomputed=Pconcept-GX-Fsign-q²Fzero.

The packed-index residual therefore differs from its stated polynomial
by `2(GX+Fsign+q²Fzero)`. Those three simple residuals are placed
before it in the certificate. The previous auxiliary-norm correction
is retained exactly and remains acyclic. Every other predecessor source
polynomial is unchanged, except the replaced packed polynomial and the
one added width equation.

## 3. All preliminary bounds precede power recovery

Equation (2), positivity of z, and (1) give

    R-1>(B0-1)Zon>=8Zon.

In particular R>=9, W=R³ and q=Wv>=R³. Also

    SH<J, (hs+hz)H<J/32,
    RK-g>R+gI.                                               (6)

For the last inequality, R>g(I+1) and K>=2 imply
R(K-1)>g(I+1). The other inequalities follow from H(R-1)=2J;
the chosen margins in (1) are stronger than needed.

The positive flag pairs give 0<Kplus,Kminus,Z,D<H. Hence

    0<t<(R-3)H/6<J/3.                                       (7)

Writing A=A0+A1 and delta=Kplus-Kminus>-H, the time equation gives

    A<WH/(W-1)<J.                                           (8)

The last inequality follows already from R>=9. Consequently
`-J<t-Ai<J/3` for both tracks.

From (5), P>0. Equations (3) imply

    r=(q^12-1)/2+P<q^12,
    P<=(q^12-1)/2.                                         (9)

The top program pair yields a useful sharp bound. All remaining terms
in (5) are positive, so

    P >= q^10[(q-1)V+zH].                                  (10)

If V>=J+1, the right side is at least
`q^10[(q²-1)/2+1]>(q^12-1)/2`, since zH>=1. Therefore
V<=J. Dropping the positive zH term would only give V<=J+1;
that endpoint is not silently discarded.

Let O=V+hs*Kplus+hz*D. By (6), O<J+J/32<q. The unchanged
cyclic route and RK-g>R+gI now give C<q. Thus

    -q<SH-C<J.                                             (11)

Finally, (2) and the head geometry give

    0<zH<hgrid*H=(q-1)/(B0-1)<=J/4,
    -J<zH-V<J/4.                                          (12)

All these conclusions use integer equations and positivity only.
They do not assume that q or R is a power of three, or that any
computed complement has Boolean digits.

Because q>=R³ and R>=9, D0=q^12>=81. Equation (9) gives
r>=27, r<2D0 and D0<r². These are exactly the preliminary
hypotheses of the retained general43-operation kernel. Its soundness
does not assume even r. Applying it now proves that D0, and therefore
q, is a power of three, and that D0 divides the central binomial
coefficient of r.

## 4. Decode every pair without an incoming carry

Since 0<r<D0, the direct unit-two ternary mask theorem gives native
digits one or two for r, with unit digit two. Subtracting the full
repunit (D0-1)/2 has no borrow. Thus P is a Boolean ternary word
with unit digit one, and each of its base-q chunks is at most J.

The first four coefficients Kplus,Kminus,Z,D are positive and less
than H<q. They therefore equal their successive Boolean chunks and
produce no carry. This handles both sign and zero pairs explicitly.

Next consider t-A0. If it were negative, (7)-(8) would make its
normalized chunk `q+t-A0>q-J>J`, impossible. Hence it is
nonnegative and less than q. The following A0<J is also exact.
The same argument decodes t-A1 and A1. No carry reaches the
program fields.

For the state pair, put TC=SH-C. If TC<0, (11) gives exactly
one borrow into the next field. Its low chunk cap implies

    q+SH-C<=J, hence C>=J+1+SH.

The next coefficient is C-1, which lies in [0,q). Its cap implies
C<=J+1, contradicting SH>0. Thus TC>=0. Since TC<SH<J,
both TC and the following C are exactly their Boolean chunks.

For the last pair, TV=zH-V lies strictly above -J by (12).
A negative value would normalize to a chunk greater than J.
Therefore TV>=0, TV<J, and the final V<=J is also exact.
All twelve fields in (4) have been decoded, with no ignored carry
or borrowed high chunk.

## 5. Recover the grid, state support, and complete computation

The equations q=Wv and W=R³ imply that R is a power of three.
Since 3^ell-1 divides R-1 and R>1, the usual order identity for
powers of three gives R=3^m with ell dividing m. The head equation
then gives q=R^u and H=1+R+...+R^(u-1), with u>=3.

Thus hgrid=(R-1)/(B0-1) is the word with one at every ell-grid
position of an R block. Zon<hgrid is Boolean on those positions,
so z=hgrid-Zon is its digitwise complement. Multiplication by H
repeats it in disjoint R blocks. Accordingly zH is the global grid
word with precisely Zon*H removed.

The two Boolean words V and TV satisfy V+TV=zH. Adding two
Boolean ternary words has raw coefficients at most two and therefore
no carry. Each is consequently supported in that allowed grid word.
In particular V has no off-grid digits and avoids every old forbidden
position: old on-grid positions were included in Zon, and old
off-grid positions are absent from the global grid.

Likewise, C+TC=SH and both summands are Boolean. The fixed word S
fits inside R and is Boolean, so C is supported in the
allowed state positions. Both flag pairs sum to H; their Boolean
digits likewise show that they are disjoint row-head subsets.

These are the complete support and label hypotheses of the previous
cyclic controller proof. Its fixed-row bounds hold because (1)-(2)
put R above (K+g)(S+1), all output constants, and the forbidden
mask. The same count marker proves one state per row, the route
selects legal successive states, and the emitted signs and zero
requests equal the typed row-head words. The first Kplus digit is
one, as required by the fixed prefix.

Set T=J-t>0. The Boolean fields t-Ai give Boolean old guards
`Ai+T=J-(t-Ai)`. Together with the typed flag pairs and the unchanged
time equation, they meet the proved raw-counter decoding interface.
It recovers a finite nonnegative three-register history from
`[2x,0,0]` to the all-zero bank, including the required source-zero
tests. The parity-aligned counter proof also establishes complete
banks before relying on program phases. Thus every new positive
solution is an accepting computation of the same compiled machine.
No new machine-universality assertion is substituted for that existing
compiler theorem.

## 6. Positive converse and the changed Pell index

Conversely take any accepting finite computation of the predecessor's
compiled machine. Enlarge the counter width to m divisible by ell,
so that R=3^m contains every source value below R/3, satisfies the
input bound, and has hgrid>Zon. Define z=hgrid-Zon>0.
All previous raw track, flag, head, and program words can be chosen
for this enlarged width. The prefix and cleanup ensure positivity
of both tracks, both sign words, Z and D, C and V. In particular
the old positive gap t and every supplied variable remain positive.

The old Boolean guards give Boolean complements t-Ai. State support
gives the Boolean complement SH-C. Correct ROM junk is on-grid and
avoids Zon, whose added high bit exceeds every correct row product.
It therefore has the Boolean complement zH-V. Zeros among these
computed complements are allowed. This proves all twelve masks in
(4), and the exact outer equations follow from their definitions.

Pack these fields into P and set r=P+(q^12-1)/2. All digits of r
are native, its unit is two, and beta=q^12-r is positive. The
required central divisibility follows from the ternary carry theorem.

The fixed-sign positive Pell converse additionally needs even r.
This is checked independently. The total of the twelve fields is

    2H+2t+(S+z)H.

Every valid counter path from an even initial bank to zero has even
serial duration u, so H is even. The displayed sum is even. Since
q is odd, P is even; since q^12=1 mod4, the added wide repunit
is even too. Thus r is even. The general43-operation converse at
the actual scale D0=q^12 supplies every remaining positive auxiliary.
This completes both directions for the same represented predicate.

## 7. Verification boundary

The companion checks all23 expanded source comparisons and the complete
102-operation schedule. It also tests signed program-pair rejection,
the sharp V=J+1 endpoint, and disjoint Boolean sums. Its two canonical
examples are recomputed at the new grid-aligned widths and with the
new field order; they check every outer source, all twelve masks,
positive slacks, parity, and exact central valuations. They do not
numerically instantiate the enormous Pell auxiliaries. Those are
supplied by the general positive converse proved above.

The author gate and three independent full proof/source reviews and
fresh complete verification runs passed without mathematical findings.
They reproduced 54 multiplications, 48 additions or subtractions,
35 positive unknowns, and 23 equations. The finite checks include
2,126 signed pair windows, 1,862 rejected negative state complements,
555 rejected negative junk complements, and 3,276 disjoint Boolean
sums. The two fresh canonical examples have width 1,510 and central
valuations 217,440 and 326,160. Publication and the established
90-operation frontier remain separate from this alternate-architecture
milestone.
