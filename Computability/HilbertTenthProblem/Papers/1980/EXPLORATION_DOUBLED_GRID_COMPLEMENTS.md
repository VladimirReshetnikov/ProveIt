# Doubled grid-complement packing in 101 operations

The six-pair construction in `EXPLORATION_INTERLEAVED_GRID_COMPLEMENTS.md`
admits a further saving by doubling its raw coordinates. The resulting
count is **101 operations:55 multiplications and46 additions or
subtractions**, with **35 positive unknowns and23 equations**. All twelve
mask fields remain. The fixed global-grid geometry is retained, and its
new scalar z is not doubled. This improves the alternate complete
raw-counter/controller architecture; the established universal frontier
remains90.

The exact source/checker is
`../verification/explore_doubled_grid_complements.py`, with an adjacent
JSON receipt. The proof below establishes a complete construction, not
just the syntactic saving. Signed complement pairs can hide odd
coordinates locally. The controller's cyclic initial residue excludes
the state-pair borrow, and a structural terminal label excludes both
counter-pair borrows.

## 1. Source, program convention, and counted saving

Use the fixed constants and grid of102. Keep every source name, but let

    J,H,t,A0,A1,Kplus,Kminus,Z,D,C,V

denote twice the old raw coordinates. Here t is the supplied Tgap.
The width R, q,W,v,z, input x, packed index, slack beta, and all Pell
coordinates are not doubled. The input slack changes as specified below.

The compiled graph has the following structural property:

    Every edge entering the cyclic initial vertex has a source
    whose zero-request label is zero.                         (1)

This is already true of the universal compiler in
`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`. Every logical
instruction consists of two physical banks. Its second bank has no
zero requests, including the zero branch of an instruction. Only the
end of such a complete macro enters the accepting halt. The fixed
prefix has the same property. Identifying that halt with the initial
vertex preserves its incoming edges. Thus(1) is a property of the
labelled graph before any numerical counter semantics are recovered.
It also holds for every incoming edge of the checker's fixed example.

Let X and the conceptual packed fields be

    X=Kminus+q²[D+q²(A0+q²(A1+q²(C+q²V)))],
    Kplus,Kminus,Z,D,t-A0,A0,t-A1,A1,SH-C,C,zH-V,V.

Their concatenation is still

    P=(q-1)X+(1+q²)(H+q^4 t)+q^8 H(S+q²z).                  (2)

The thirteen outer source equations now read

    q=J+1, q=Wv, W=R³, H(R-1)=2J,
    Kplus+Kminus=H, Z+D=H,
    (B0-1)(Zon+z)=R-1,
    6t=(R-3)D,
    W(A0+A1+Kplus-Kminus)=A0+A1-4x,
    4x+alphaI=R,
    2r+1=q^12+P, r+beta=q^12,
    (RK-g)C=gI(2J)+R(V+hs*Kplus+hz*D).                      (3)

The same ten fixed-sign43-operation Pell equations use D0=q^12.
All supplied unknowns and the parameter x are positive. The computed
complements may a priori be signed; no new positivity assumption is
imposed on them.

The existing q right side uses J+1 instead of2J+1. The packed product
uses JX instead of(2J)X; the old twice_J register remains needed for
the head and route equations. Replace the one addition x+x by the
one product4*x, and delete the final addition doubling P. The packed
right side becomes q^12+P. Hence

    102=54M+48A  -->  101=55M+46A.

Neither the power chain nor the two-operation grid condition changes.

For exact source accounting, set G=q-J-1 and let Fsign,Fzero be the
two positive-pair residuals. The computed packed register equals

    Pconcept-GX-Fsign-q²Fzero.

The new packed-index residual therefore has correction
`GX+Fsign+q²Fzero`, without the old factor two. Its dependencies precede
it. The old auxiliary-norm correction is retained. The checker expands
all23 comparisons and also verifies the divided-coordinate source map
in Section7 exactly.

## 2. Preliminary bounds without a digit assumption

Initially q=J+1 only gives q>=2. The paid width equation and fixed
choice of Zon from102 give

    R-1>(B0-1)Zon>=8Zon,
    Zon>max(4S,8(hs+hz),g(I+1),(K+g)(S+1),81).

In particular R>=27, W=R³, q>=R³, R>2gI and R>g. These conclusions
precede the Pell kernel. The head equation gives

    H=2J/(R-1), SH<J, (hs+hz)H<J/32.

The retained positive flag pairs give0<Kplus,Kminus,Z,D<H, and

    0<t<(R-3)H/6<J/3.                                     (4)

Write A=A0+A1 and delta=Kplus-Kminus>-H. The time equation implies

    0<A<WH/(W-1)<J/4.                                    (5)

The last inequality holds for R>=27. In particular every track is
less than q, while -q<t-Ai<q. A negative guard field can cause one
borrow into its following track, but that track cannot carry into the
next pair.

The factored expression(2) is positive without any complement bounds.
The two packed equations give

    0<P<=q^12-1,   r=(q^12+P-1)/2<q^12.                  (6)

Its top pair satisfies

    P>=q^10[(q-1)V+zH].

If V>=q+1, this is at least q^12, since zH>=1. Hence V<=q.
The possible endpoint V=q is retained at this stage. Also

    0<zH<(q-1)*2/(B0-1)<=J/4,
    -q<zH-V<J/4.                                         (7)

Set O=V+hs*Kplus+hz*D. Then O<33q/32. The fixed width gives
g+2gI<R/4, and K>=3, so

    RK-g>2gI+(33/32)R.

Comparing this with the route right side in(3) proves C<q.
Consequently -q<SH-C<J. These bounds do not use Booleanity or parity
of any computed field.

Finally(6), q>=R³ and P>0 imply D0>=81, r>=27, r<2D0 and D0<r².
These are the hypotheses of the general43-operation kernel. Apply
its soundness now to recover q as a power of three and D0 dividing
the central binomial coefficient of r. Soundness does not require
an assumed even r.

## 3. Power geometry and the doubled mask

Write q=3^e. Since R³ divides q, R=3^m. The head equation initially
only gives R-1 dividing2(q-1). To justify cancellation of the factor
two, write e=um+s with0<=s<m. Then

    R-1 divides2(3^s-1),
    0<=2(3^s-1)<=2(R/3-1)<R-1.

Thus s=0, q=R^u, u>=3, and H is twice the row-head repunit. In
particular H,J are even. The paid grid equation gives ell dividing m
and hgrid=Zon+z=(R-1)/(B0-1), exactly as in102.

Since r<D0, the unit-two mask theorem says that r has only ternary
digits one or two, with unit digit two. Subtracting the full repunit
(D0-1)/2 has no borrow. Therefore

    P=2[r-(D0-1)/2]

has only ternary digits zero or two, with unit digit two. Every
base-q chunk of P is even, at most q-1, and becomes Boolean after
division by two. This conclusion applies to normalized chunks, not
yet to every formal coefficient in(2).

## 4. Recover the controller while skipping the track borrows

The first four coefficients Kplus,Kminus,Z,D are positive and less
than H<q. They are their actual doubled chunks, so they are even
and there is no incoming carry to the first guard pair. Equation(4)
now gives t even: (R-3)/6 is an integer, and D is even.

For a guard pair (t-Ai,Ai), the low coefficient lies in(-q,q) and
the upper coefficient is positive and less than q. If the low field
is nonnegative, both normalize without a carry. If it is negative,
exactly one borrow replaces the high coefficient by Ai-1, still in
[0,q). Thus either pair has no outgoing carry. We can pass both
pairs without deciding their signs.

Put TC=SH-C. Its bounds similarly allow at most one borrow, and
the normalized upper field C or C-1 lies in[0,q). If TC<0, the
mask on that upper field says

    C=2c+1, with c a Boolean ternary word.                    (8)

This possibility is excluded by the cyclic initial residue. The route
modulo R gives

    g(C-2I)=0 mod R.

The fixed g is a power of three and R>2gI, so R/g is a positive
power of three and

    C=2I mod(R/g),   0<2I<R/g.                              (9)

For any Boolean ternary word c and any power M of three,
`c mod M <= (M-1)/2`. Consequently `(2c+1) mod M` is either odd
or zero. It cannot equal the strictly positive even residue in(9).
This contradicts(8). Therefore TC>=0; TC and C are actual doubled
chunks. This argument uses the controller endpoint, not an unproved
counter-input interpretation.

The cyclic route now has even C,Kplus,D and even2J. Since R is odd,
its parity forces V even. This excludes the preliminary endpoint V=q.
The remaining TV=zH-V is even and lies in(-q,q). If it were negative,
its normalized low chunk q+TV would be odd. Thus TV>=0; both TV
and V are their actual doubled chunks, with no borrow.

Divide the four program fields, four flags and H,J by two. The
Boolean equations

    (C+TC)/2=S(H/2),   (V+TV)/2=z(H/2)

are precisely the state-support and global-grid-complement tests of102.
The grid word excludes every old forbidden position. The same fixed
coefficient bounds, count marker and cyclic endpoint argument therefore
recover a genuine controller path and its exact sign and zero labels.
This controller decoding does not read the still-undecoded tracks.

## 5. The terminal label excludes both guard borrows

The path is positive in length. By the structural compiler property(1),
its last source has zero-request label zero. Since D/2 is the complement
of that label, its last row-head is one. Consequently

    D>=2R^(u-1)=2q/R,
    t=(R-3)D/6 >= (R-3)q/(3R).                             (10)

Independently, the pretyping time bound can be sharpened in the useful
form

    A<WH/(W-1)<3q/R.                                      (11)

For R>=27 one has (R-3)/3>3. Equations(10)-(11) give t>A, hence
both t-A0 and t-A1 are strictly positive. There are no guard borrows.
All four guard/track fields are therefore actual doubled chunks, and
both supplied tracks are even.

There is no assumption here that the last numerical counter is already
known to be positive, or that the counter history has already been
decoded. The sole terminal premise is the fixed graph's absence of a
zero request on its accepting predecessors. Without a premise such as
this, local doubled guard masks do admit odd-track aliases; the checker
records one explicitly.

## 6. Complete soundness

Every one of the eleven doubled supplied coordinates is now even.
Dividing them by two restores the positive coordinates of102, including
its positive t and both retained positive flag pairs. The scalar z and
all powers and program constants stay unchanged. Set

    alphaI_old=alphaI_new+2x>0.

Then the old input equation2x+alphaI_old=R holds. Every other old
outer source is the new source or one half of it. In particular the
packed word is divided by two, so the old equation
`2r+1=q^12+2Pold` has the same r,beta and all the same Pell coordinates.
The checker verifies each polynomial factor of this transport exactly.

The complete102 counter/controller theorem consequently proves an
accepting computation of the same compiled ordinary-input machine.
This restores counter nonnegativity, all source-zero tests, complete
banks and the first-return acceptance contract, rather than assuming
any of them during the borrow proof.

## 7. Positive converse and evidence scope

Take a canonical accepting102 computation of this compiled machine.
Choose its grid-aligned radix wide enough that R>4x, in addition to
the old width and source-value bounds. Double J,H,t,Ai, both flag
pairs and C,V, and keep z. Define alphaI=R-4x>0. Every supplied
coordinate remains positive, and each conceptual field is exactly
twice its old value. Thus P=2Pold and the new packed equation has
exactly the old r and beta at this enlarged width.

The old102 parity proof gives even r. Its native unit condition,
central divisibility and complete positive43-operation Pell construction
therefore apply unchanged. This establishes both directions for the
same represented input predicate. It does not assert that every old
small-width witness meets the stronger input bound.

The companion checks the full101 schedule, all23 source comparisons,
the conditional divided-coordinate polynomial transport, the odd-residue
lemma, nonvacuous signed pair aliases, power geometry and the terminal
gap inequality. A focused structural check also calls the actual
physical-phase generator for all three registers' increment and both
conditional branches, plus a jump; it compiles the sample machine and
its cyclic quotient and verifies every accepting predecessor's zero
label. This check does not assume a valid numerical trace. Two canonical
examples are built freshly at the actual
grid width, with every outer residual, all twelve masks, positivity,
parity and exact central valuation checked. Their enormous Pell
auxiliaries are supplied by the proved general converse rather than
materialized numerically. The author gate and three independent complete
proof/source reviews and fresh full verification runs pass, with no
findings. All three reviewers also independently read and reran the
focused generic terminal-compiler check added after the first author
run. These gates are separate from publication and from the established
90-operation frontier.
